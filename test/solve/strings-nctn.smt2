; a concatenation whose constants do not fit in a constant, in order
; (`STRINGS_F_NCTN`): certified as cvc5's proof, by regular expressions
; (`StringsCore.proveNctn`)
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun w () String)
(assert (str.contains "AFBCDEFG" (str.++ x "C" y "F" z "E" w)))
(check-sat)
