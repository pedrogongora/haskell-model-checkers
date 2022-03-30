module ModelParser where

data Value = Val Bool | Val Int | Val String

type EnumDomain = [String]

data VariableType = BooleanType | IntegerType | EnumType EnumDomain

data VariableDef = VarDef String VariableType

data ArithmeticExp = Add ArithmeticExp ArithmeticExp   |
                     Sub ArithmeticExp ArithmeticExp   |
                     Times ArithmeticExp ArithmeticExp |
                     Div ArithmeticExp ArithmeticExp   |
                     Minus ArithmeticExp               |
                     Lit Int                           |
                     Var String

data BooleanExp = And BooleanExp BooleanExp       |
                  Or BooleanExp BooleanExp        |
                  Not BooleanExp                  |
                  GEq ArithmeticExp ArithmeticExp |
                  LEq ArithmeticExp ArithmeticExp |
                  GT ArithmeticExp ArithmeticExp  |
                  LT ArithmeticExp ArithmeticExp  |
                  Eq ArithmeticExp ArithmeticExp  |
                  Const Bool                      |
                  Prop String

data ModuleDef = 
