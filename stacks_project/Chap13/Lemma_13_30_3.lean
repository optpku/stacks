/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.HomotopyCategory.QuasiIso
import ReasLib.CategoryTheory.Adjunction.Derived.Total
import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.30.3

Essential constancy of the pointwise presentations at every object turns the comparison of
Lemma 13.30.2 into the canonical adjunction between the total left- and right-derived functors.
Here derived categories are the neutral quasi-isomorphism localizations of the homotopy categories
of cochain complexes.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  {F : 𝒜 ⥤ ℬ} {G : ℬ ⥤ 𝒜}
  [F.Additive] [G.Additive]
  (adj : G ⊣ F)

/- Lemma 13.30.3 (Stacks 09T5): if the cochain left- and right-derived presentations of an
adjoint pair are essentially constant everywhere, their total derived functors are adjoint. -/
@[stacks 09T5]
#check @CategoryTheory.Adjunction.Total.adjunction

end CategoryTheory.Adjunction
