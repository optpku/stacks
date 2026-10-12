/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap108.Lemma_108_8_5_Smooth
public import stacks_project.Chap109.Lemma_109_16_5_Substack
public import stacks_project.Chap109.Lemma_109_22_7
public import stacks_project.Chap109.Lemma_109_25_1
public import stacks_project.Chap109.Theorem_109_25_3_DeligneMumford
public import stacks_project.Chap109.Theorem_109_25_3_Proper

/-!
# Properties of the moduli stack of stable curves of genus `g`

For `g ≥ 2`, the algebraic stack `ℳ̄_g` is a Deligne–Mumford stack, proper and
smooth over `Spec(Z)`, and the locus `ℳ_g` of smooth curves is a dense open
substack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.ObjectProperty
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The structure morphism of a full subcategory of `𝒞urves` equals the
composite of its inclusion into `𝒞urves` with the structure morphism of
`𝒞urves`. -/
theorem toIdentitySlice_ofObjectProperty {S : Scheme.{u}}
    (Q : ObjectProperty (Obj S))
    [Functor.IsFibered.InGroupoids (Q.ι ⋙ p S)] :
    CohStack.toIdentitySlice (ofObjectProperty Q) =
      inclusionOf Q ≫ CohStack.toIdentitySlice (toGroupoids S) :=
  sorry

/-- The full subcategory of `𝒞urves` cut out by `smoothH0OfGenus g` is fibred in
groupoids over `Over S`. -/
instance instIsFiberedInGroupoids_smoothH0OfGenus (g : ℕ) (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids ((smoothH0OfGenus g S).ι ⋙ p S) :=
  sorry

/-- The full subcategory of `𝒞urves` cut out by `smoothH0OfGenus g` is an
algebraic stack in the Hom-universe of `CohStack.toGroupoids`. -/
instance instAlgebraicStack_ofObjectProperty_smoothH0OfGenus
    (g : ℕ) (S : Scheme.{u}) :
    CohStack.AlgebraicStack (ofObjectProperty (smoothH0OfGenus g S)) :=
  sorry

/-- For `2 ≤ g`, membership in `smoothH0OfGenus g` implies membership in
`stableOfGenus g`. -/
theorem smoothH0OfGenus_le_stableOfGenus (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u}) :
    smoothH0OfGenus g S ≤ stableOfGenus g S :=
  sorry

/-- The inclusion of `ℳ_g` into `ℳ̄_g`, as a 1-morphism of categories
fibred in groupoids over `Over S`. -/
def inclusionSmoothStableOfGenus (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u}) :
    ofObjectProperty (smoothH0OfGenus g S) ⟶
      ofObjectProperty (stableOfGenus g S) :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    { toFunctor := ιOfLE (smoothH0OfGenus_le_stableOfGenus g hg S)
      w := sorry }

/-- The underlying functor of `inclusionSmoothStableOfGenus g hg S` is the
identity-on-carriers map of `smoothH0OfGenus_le_stableOfGenus`. -/
theorem inclusionSmoothStableOfGenus_toFunctor
    (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u}) :
    FiberedCategoryOver.Groupoids.toFunctor
        (inclusionSmoothStableOfGenus g hg S) =
      ιOfLE (smoothH0OfGenus_le_stableOfGenus g hg S) :=
  sorry

/-- Theorem 109.25.3 (1): for `g ≥ 2`, the algebraic stack `ℳ̄_g` of stable
genus-`g` curves is a Deligne–Mumford stack. -/
@[stacks 0E9C]
instance instDeligneMumfordStack_stableOfGenus (g : ℕ) [Nat.AtLeastTwo g] :
    CohStack.DeligneMumfordStack
      (ofObjectProperty (stableOfGenus g specZ)) :=
  sorry

/-- Theorem 109.25.3 (2): for `g ≥ 2`, the structure morphism
`ℳ̄_g ⟶ Spec(Z)` is proper. -/
@[stacks 0E9C]
instance instProper_stableOfGenus (g : ℕ) [Nat.AtLeastTwo g] :
    CohStack.Hom.Proper
      (CohStack.toIdentitySlice (ofObjectProperty (stableOfGenus g specZ))) :=
  sorry

/-- Theorem 109.25.3 (3): for `g ≥ 2`, the structure morphism
`ℳ̄_g ⟶ Spec(Z)` is smooth. -/
@[stacks 0E9C]
instance instSmooth_toIdentitySlice_stableOfGenus (g : ℕ) [Nat.AtLeastTwo g] :
    CohStack.Hom.Smooth
      (CohStack.toIdentitySlice (ofObjectProperty (stableOfGenus g specZ))) :=
  sorry

/-- Theorem 109.25.3 (4): for `g ≥ 2`, the locus `ℳ_g` parametrizing smooth
curves is a dense open substack of `ℳ̄_g`. -/
@[stacks 0E9C]
theorem isDenseOpen_smoothH0OfGenus (g : ℕ) (hg : 2 ≤ g) :
    CohStack.Hom.OpenImmersion (inclusionSmoothStableOfGenus g hg specZ) ∧
      Dense (Set.range (CohStack.Points.map
        (inclusionSmoothStableOfGenus g hg specZ))) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
