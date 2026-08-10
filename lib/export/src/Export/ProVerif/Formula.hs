-- |
-- Pure formula construction and traversal helpers used during preparation.
module Export.ProVerif.Formula
  ( buildConjunction,
    buildDisjunction,
    formulaContainsAction,
  )
where

import Theory

buildConjunction :: [LNFormula] -> LNFormula
buildConjunction [] = TF True
buildConjunction [formula] = formula
buildConjunction formulas = foldr1 (.&&.) formulas

buildDisjunction :: [LNFormula] -> LNFormula
buildDisjunction [] = TF False
buildDisjunction [formula] = formula
buildDisjunction formulas = foldr1 (.||.) formulas

formulaContainsAction :: LNFormula -> Bool
formulaContainsAction =
  foldFormula
    (\atom -> case atom of Action _ _ -> True; _ -> False)
    (const False)
    id
    (\_ left right -> left || right)
    (\_ _ body -> body)

