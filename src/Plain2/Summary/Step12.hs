module Plain2.Summary.Step12 where

import Expr
import Plain2.AExpr
import Plain2.Summary.Step11 (convK)

-- Step12 packages the Plain2 conversion as the identity-continuation instance
-- of the final `convK` equations.
conv :: Expr -> AExpr
conv expr = convK expr ATerm
