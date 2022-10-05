# -*- coding: utf-8 -*-
"""
Created on Tue Oct  4 15:06:44 2022

"""

# standard packages
from sklearn.tree import _tree
import sys

# pip install lark-parser
import lark

# local packages
import dautils


class Model2CLP:
    def __init__(self, pred_atts, target, df_code):
        self.pred_atts = pred_atts
        self.target = target
        self.df_code = df_code
        self.feature_names = df_code.encoded_atts(pred_atts)
        self.constraints = []
        self.instances = dict()
        self.model = ""
        self.transform = self.Parse(self)
        self.parse = lark.Lark(self.grammar_exp, parser='lalr', transformer=self.transform).parse

    def reset(self):
        self.constraints = []
        self.instances = dict()
        self.model = ""
    
    grammar_exp = """
        ?start: seqc
        ?seqc: cons
            | seqc "," cons       -> seq
        ?cons: exp "<" exp        -> lt
            | exp "<=" exp        -> le
            | exp "=" exp         -> eq
            | exp ">=" exp        -> ge
            | exp ">" exp         -> gt
            | cons "<=>" cons     -> iff
        ?exp: product
            | exp "+" product   -> add
            | exp "-" product   -> sub
        ?product: atom
            | product "*" atom  -> mul
            | product "/" atom  -> div
        ?atom: NUMBER           -> number
             | "-" atom         -> neg
             | NAME "." NAME    -> var
             | NAME             -> val
             | "(" exp ")"
        %import common.CNAME    -> NAME
        %import common.NUMBER
        %import common.WS_INLINE
        %ignore WS_INLINE
    """       

    class Parse(lark.InlineTransformer):
        
        def __init__(self, m2=None):
            self.m2 = m2
    
        def number(self, value):
            return ['number_const', str(float(value))]
    
        def val(self, value):
            return ['val', value]
    
        def var(self, inst, var):
            if self.m2 is not None:
                if inst not in self.m2.instances:
                    raise ValueError("unknown instance "+inst)
                if var not in self.m2.pred_atts:
                    raise ValueError("unknown var "+var)
            return ['var', inst, var]
        
        def add(self, left, right):
            return ['+', left, right]
        
        def sub(self, left, right):
            return ['-', left, right]
        
        def mul(self, left, right):
            return ['*', left, right]
        
        def div(self, left, right):
            return ['/', left, right]
        
        def neg(self, left):
            return ['-', left]
        
        def lt(self, left, right):
            return ['<', left, right]
        
        def le(self, left, right):
            return ['=<', left, right]
           
        def eq(self, left, right):
            if left[0]=='var' and right[0]=='val':
                var, val = left[2], right[1]
                if self.m2 is not None and var in self.m2.df_code.nominal and val not in self.m2.df_code.encode[var]:
                    raise ValueError("value not in domain " + val)
                left[2] += '_'+val
                return ['=', left, ['number_const', '1']]
            if left[0]=='var' and right[0]=='var':
                inst1, inst2 = left[1], right[1]
                var1, var2 = left[2], right[2]
                if self.m2 is not None:
                    var1n, var2n = var1 in self.m2.df_code.nominal, var2 in self.m2.df_code.nominal
                    if var1n or var2n:
                        if var1n and var2n:
                            d1 = set(self.m2.df_code.encode[var1].keys())
                            d2 = set(self.m2.df_code.encode[var2].keys())
                            if d1 != d2:
                                raise ValueError("equality between different domains "+var1+" "+var2)
                            res = []
                            for v in d1:
                                con = ["=", ['var', inst1, var1+'_'+v], ['var', inst2, var2+'_'+v]]
                                res = [',', con, res] if res != [] else con
                            return res
                        raise ValueError("equality between different types "+var1+" "+var2)                    
            return ['=', left, right]
           
        def ge(self, left, right):
            return ['=<', right, left]
           
        def gt(self, left, right):
            return ['<', right, left]
           
        def iff(self, left, right):
            # check types
            assert left[0]=='=' and right[0]=='='
            assert left[1][0]=='var' and right[1][0]=='var'
            assert left[2][0]=='number_const' and right[2][0]=='number_const'
            left1 = ['var', left[1][1], left[1][2]] 
            right1 = ['var', right[1][1], right[1][2]] 
            return ['=', left1, right1]
                
        def seq(self, left, right):
            return [',', left, right]

        def toCLP(self, tree):
            op = tree[0]
            if op=='number_const':
                return tree[1]
            if op=='val':
                return tree[1]
            if op=='var':
                return 'var(i'+tree[1]+', v'+tree[2]+')'
            if op in {'+', '*', '/', '=<', '<', '=', ','}:
                return self.toCLP(tree[1]) + op + self.toCLP(tree[2])
            if op=='-' and len(tree)==3:
                return self.toCLP(tree[1]) + '-' + self.toCLP(tree[2])
            if op=='-' and len(tree)==2:
                return -self.toCLP(tree[1])
            raise "unknown operator"

            
    
    def toCLP(self, o=sys.stdout):
        # header
        o.write(":- use_module(library(clpr)).")
        o.write("\n:- use_module(library(lists)).")
        # features
        o.write("\n% feature(i, constant) :- constant name for the i-th variable")
        for i, f in enumerate(self.feature_names):
            o.write('\nfeature({}, v{}).'.format(i, f))
        nf = len(self.feature_names)
        o.write('\nnfeatures({}).'.format(nf))
        # instances
        for name, (n, _) in self.instances.items():
            o.write("\ninstance({}, i{}).".format(n, name))
        # model
        o.write(self.model)
        # test clause
        Cs = ", ".join(c for c in self.constraints)
        Labs = ", ".join(str(label) for _, (_, label) in self.instances.items())
        o.write("""\ntest(Vars) :- 
            nfeatures(N), 
            length(Vars, {}),
            lengths(Vars, N),
            paths(Vars, [{}], CCs),
            tells_cs(CCs),
            exp2cons([{}], Vars, Cs),
            tell_cs(Cs).""".format(len(self.instances), Labs, Cs))
        o.write("\n:- ['post.pl'].")
        
    def instance(self, name, label):
        if name in self.instances:
            raise "instance "+name+" exists already"
        n = len(self.instances)
        self.instances[name] = (n, label)        
        
    def model_tree(self, tree):
        tree_ = tree.tree_
        classes_ = tree.classes_
        feature_pos = {f:i for i, f in enumerate(self.feature_names)}
        feature_name = [
            feature_pos[self.feature_names[i]] if i != _tree.TREE_UNDEFINED else "undefined!"
            for i in tree_.feature
        ]
        nf = len(self.feature_names)
        res = "% path(Vars, Constraint, Pred, Conf) :- Constraint in a path of a decision tree over Vars with prediction Pred and confidence Conf"
        def recurse(node, depth, body="", varset=set()):
            if tree_.feature[node] != _tree.TREE_UNDEFINED:
                var = feature_name[node]
                name = 'X' + str(var)
                threshold = tree_.threshold[node]
                if body != '':
                    body = body + ','
                body_left = body + "{} =< {}".format(name, threshold)
                varset = varset | set([var])
                res_left = recurse(tree_.children_left[node], depth + 1, body_left, varset)
                body_right = body + "{} > {}".format(name, threshold)
                res_right = recurse(tree_.children_right[node], depth + 1, body_right, varset)
                return res_left + "\n" + res_right
            else:
                freqs = tree_.value[node][0]
                pred, maxfreq = dautils.argmax(freqs)
                maxfreq /= sum(freqs)
                allf = ','.join( ('X'+str(i) if i in varset else '_') for i in range(nf) )
                return "path([{}], [{}], {}, {}).".format(allf, body, classes_[pred], maxfreq)
        self.model = res + "\n" + recurse(0, 1)
    
    def constraint(self, con):
        # linear expression on continuous/ordinal features
        self.constraints.append(self.transform.toCLP(self.parse(con)))
        
        