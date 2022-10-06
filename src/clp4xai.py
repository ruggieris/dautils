# -*- coding: utf-8 -*-
"""
Created on Tue Oct  4 15:06:44 2022

"""

# standard packages
from sklearn.tree import _tree
from sklearn.tree import DecisionTreeClassifier

import sys

# pip install lark-parser
import lark
# pip install lineartree
from lineartree import LinearTreeClassifier

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
        self.model_ = ""
        self.transform = self.Parse(self)
        self.parse = lark.Lark(self.grammar_exp, parser='lalr', transformer=self.transform).parse

    def reset(self):
        self.constraints = []
        self.instances = dict()
        self.model_ = ""
    
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
                # inst.var = val
                var, val = left[2], right[1]
                if self.m2 is not None and var in self.m2.df_code.nominal and val not in self.m2.df_code.encode[var]:
                    raise ValueError("value not in domain " + val)
                left[2] += '_'+val
                return ['=', left, ['number_const', '1']]
            if left[0]=='var' and right[0]=='var':
                # inst1.var1 = inst2.var2
                inst1, inst2 = left[1], right[1]
                var1, var2 = left[2], right[2]
                if self.m2 is not None:
                    var1n, var2n = var1 in self.m2.df_code.nominal, var2 in self.m2.df_code.nominal
                    if var1n or var2n:
                        # at least one var1 or var2 nominal
                        if var1n and var2n:
                            # var1 and var2 nominal
                            d1 = set(self.m2.df_code.encode[var1].keys())
                            d2 = set(self.m2.df_code.encode[var2].keys())
                            if d1 != d2:
                                raise ValueError("equality between different domains "+var1+" "+var2)
                            res = []
                            for v in d1:
                                con = ["=", ['var', inst1, var1+'_'+v], ['var', inst2, var2+'_'+v]]
                                res = [',', con, res] if res != [] else con
                            return res
                        # one but not both var1 and var2 nominal
                        raise ValueError("equality between different types "+var1+" "+var2)                    
            return ['=', left, right]
           
        def ge(self, left, right):
            return ['=>', left, right]
           
        def gt(self, left, right):
            return ['>', left, right]
           
        def iff(self, left, right):
            # inst1.var1 = val1 <=> inst2.var2 = val2 
            # arrives already transformed by eq() as
            # inst1.var1_val1 = 1 <=> inst2.var2_val2 = 1
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
            if op in {'+', '*', '/', '=<', '<', '=', ',', '=>'}:
                return self.toCLP(tree[1]) + op + self.toCLP(tree[2])
            if op=='-' and len(tree)==3:
                return self.toCLP(tree[1]) + '-' + self.toCLP(tree[2])
            if op=='-' and len(tree)==2:
                return -self.toCLP(tree[1])
            raise ValueError("unknown operator"+op)        
    
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
        o.write(self.model_)
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
        
    def model(self, clf, round_coef=2):
        nf = len(self.feature_names)
        res = "\n% path(Vars, Constraint, Pred, Conf) :- Constraint in a path of a decision tree over Vars with prediction Pred and confidence Conf"
        if isinstance(clf, DecisionTreeClassifier):
            tree_ = clf.tree_
            classes_ = clf.classes_
            feature_pos = {f:i for i, f in enumerate(self.feature_names)}
            feature_name = [
                feature_pos[self.feature_names[i]] if i != _tree.TREE_UNDEFINED else "undefined!"
                for i in tree_.feature
            ]
            def recurse(node, body="", varset=set()):
                if tree_.feature[node] != _tree.TREE_UNDEFINED:
                    var = feature_name[node]
                    name = 'X' + str(var)
                    threshold = tree_.threshold[node]
                    if body != '':
                        body = body + ','
                    body_left = body + "{} =< {}".format(name, threshold)
                    varset = varset | set([var])
                    res_left = recurse(tree_.children_left[node], body_left, varset)
                    body_right = body + "{} > {}".format(name, threshold)
                    res_right = recurse(tree_.children_right[node], body_right, varset)
                    return res_left + "\n" + res_right
                else:
                    freqs = tree_.value[node][0]
                    pred, maxfreq = dautils.argmax(freqs)
                    maxfreq /= sum(freqs)
                    allf = ','.join( ('X'+str(i) if i in varset else '_') for i in range(nf) )
                    return "path([{}], [{}], {}, {}).".format(allf, body, classes_[pred], maxfreq)
            self.model_ = res + "\n" + recurse(0)
            return
        if isinstance(clf, LinearTreeClassifier):
            tree_ = clf.summary()
            if len(clf.classes_) != 2:
                raise ValueError("only binary model trees are admissible so far")
            def recurse(n, body="", varset=set(), round_coef=round_coef):
                node = tree_[n]
                if 'col' in node:
                    var = node['col']
                    name = 'X' + str(var)
                    threshold = node['th']
                    if body != '':
                        body = body + ','
                    body_left = body + "{} =< {}".format(name, threshold)
                    varset = varset | set([var])
                    res_left = recurse(node['children'][0], body_left, varset)
                    body_right = body + "{} > {}".format(name, threshold)
                    res_right = recurse(node['children'][1], body_right, varset)
                    return res_left + "\n" + res_right
                else:
                    coef = node['models'].coef_[0]
                    coef = [(round(v, round_coef) if abs(v)>=0.01 else 0) for v in coef]
                    threshold = round(float(node['models'].intercept_[0]), round_coef)
                    varset = varset | set([i for i, v in enumerate(coef) if v != 0])
                    allf = ','.join( ('X'+str(i) if i in varset else '_') for i in range(nf) )
                    maxfreq = 1 # TBD confidence to be calculated
                    # left
                    name = '+'.join(str(v)+'*X'+str(i) for i, v in enumerate(coef) if v != 0)
                    if body != '':
                        body = body + ','
                    body_left = body + "{} =< {}".format(name, threshold)
                    body_right = body + "{} > {}".format(name, threshold)
                    left = "path([{}], [{}], {}, {}).".format(allf, body_left, node['classes'][0], maxfreq)
                    right = "path([{}], [{}], {}, {}).".format(allf, body_right, node['classes'][1], maxfreq)
                    return left + "\n" + right
            self.model_ = res + "\n" + recurse(0)
            return
        raise ValueError("unknown model " + str(clf))
    
    def constraint(self, con):
        # linear expression on continuous/ordinal features
        self.constraints.append(self.transform.toCLP(self.parse(con)))        
        