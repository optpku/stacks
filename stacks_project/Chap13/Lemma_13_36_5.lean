/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Pretriangulated.Generation.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty

-- Lemma 13.36.5: weak generation is the reusable consequence of the canonical classical
-- triangulated-generator predicate.
@[stacks 09SL] #check @CategoryTheory.ObjectProperty.IsClassicalTriangulatedGenerator.isWeak
