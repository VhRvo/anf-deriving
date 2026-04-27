module Plain1.Summary.Step12 where

import Expr
import Plain1.Summary.AExpr
import Plain1.Summary.Step11 (convK)

-- Step12 packages the original conversion as the identity-continuation
-- instance of Step11's `convK`. Step10 already isolated the two facts needed
-- to justify this specialization: `AComp` is neutral for `continueWith`, and
-- therefore `convK _ AComp` collapses back to the plain conversion.
conv :: Expr -> AExpr
conv expr = convK expr AComp