/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.HomotopyCategory.QuasiIso
import ReasLib.CategoryTheory.Adjunction.Derived.Pointwise
import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.30.2

The derived-category statement is the cochain-homotopy specialization of the neutral pointwise
derived-adjunction API.  The quasi-isomorphism localization provides both calculi of fractions;
no separate triangulated-compatibility instance is needed to construct the Hom-equivalence.
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

/- Lemma 13.30.2 (Stacks 0DVC) (1): the pointwise derived Hom-equivalence for cochain
complexes and quasi-isomorphism localizations. -/
@[stacks 0DVC]
#check CategoryTheory.Adjunction.Pointwise.homEquiv (mapHomotopyCategoryAdjunction adj)
  (HomotopyCategory.quasiIso 𝒜 (up ℤ)) (HomotopyCategory.quasiIso ℬ (up ℤ))

/- Lemma 13.30.2 (Stacks 0DVC) (2): the cochain pointwise derived Hom-equivalence is functorial
in the variable on which the left-derived functor is defined. -/
@[stacks 0DVC]
#check @CategoryTheory.Adjunction.Pointwise.HomEquiv.naturality_left

/- Lemma 13.30.2 (Stacks 0DVC) (3): the cochain pointwise derived Hom-equivalence is functorial
in the variable on which the right-derived functor is defined. -/
@[stacks 0DVC]
#check @CategoryTheory.Adjunction.Pointwise.HomEquiv.naturality_right

end CategoryTheory.Adjunction
