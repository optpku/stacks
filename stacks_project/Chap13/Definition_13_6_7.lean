/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient
import StacksCheckRecall

@[expose] public section

/-!
# Definition 13.6.7

The source quotient is the canonical Verdier localization owned by the neutral object-property
API. This entry retains the textbook notation and label without introducing a chapter-owned
quotient model.
-/

open CategoryTheory
open scoped CategoryTheory.ObjectProperty

universe v u

namespace CategoryTheory.ObjectProperty

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  (P : ObjectProperty D) [P.IsTriangulated]

@[stacks 05RI] #check (D / P)

@[stacks 05RI] #check (verdierQuotientFunctor P : D ⥤ D / P)

@[stacks 05RI] #check
  (inferInstance : (verdierQuotientFunctor P).IsLocalization P.trW)

@[stacks 05RI] #check
  (inferInstance : (verdierQuotientFunctor P).IsTriangulated)

end CategoryTheory.ObjectProperty
