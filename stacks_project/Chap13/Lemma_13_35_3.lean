/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Pretriangulated.Extension
import StacksCheckRecall

@[expose] public section

-- Lemma 13.35.3: coproduct closure of extension and direct-summand constructions is owned by
-- the reusable object-property extension API.
@[stacks 0FX3] #check @CategoryTheory.ObjectProperty.extensionProduct_isClosedUnderBinaryCoproducts

@[stacks 0FX3] #check @CategoryTheory.ObjectProperty.retractClosure_isClosedUnderBinaryCoproducts

@[stacks 0FX3] #check @CategoryTheory.ObjectProperty.extensionProductIter_isClosedUnderBinaryCoproducts
