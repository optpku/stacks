/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# The actual adic quotient diagram over a scheme

This module depends only on Mathlib. It is below the formal-space presentation
owner, so that the owner can specify the real transition maps without an import
cycle through a chapter theorem.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AdicPresentation

variable {B : Type u} [CommRing B] {S : Scheme.{u}}

/-- A quotient spectrum with its specified structure map to `S`. -/
def quotientStage (hB : Spec (.of B) ⟶ S) (J : Ideal B) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ hB)

/-- A quotient factor map, contravariantly, as an actual morphism over `S`. -/
def quotientMap (hB : Spec (.of B) ⟶ S) {J K : Ideal B} (h : J ≤ K) :
    quotientStage hB K ⟶ quotientStage hB J :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) (by
    change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ hB) = _
    rw [← Category.assoc, ← Spec.map_comp]
    rfl)

/-- The canonical stage `Spec(B/I^(n+1))` over `S`. -/
abbrev stage (hB : Spec (.of B) ⟶ S) (I : Ideal B) (n : ℕ) : Over S :=
  quotientStage hB (I ^ (n + 1))

/-- The actual adic diagram, including quotient transitions and base maps. -/
def diagram (hB : Spec (.of B) ⟶ S) (I : Ideal B) : ℕ ⥤ Over S where
  obj n := stage hB I n
  map f := quotientMap hB (Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom f)))
  map_id n := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (le_refl (I ^ (n + 1))))) = 𝟙 _
    simp
  map_comp {i j k} f g := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPow I
        (Nat.succ_le_succ (leOfHom (f ≫ g))))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPow I
        (Nat.succ_le_succ (leOfHom f)))) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPow I
        (Nat.succ_le_succ (leOfHom g))))
    simp [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factorPow]

/-- The structure map on every stage is the quotient map followed by `hB`. -/
theorem diagram_obj_hom (hB : Spec (.of B) ⟶ S) (I : Ideal B) (n : ℕ) :
    ((diagram hB I).obj n).hom =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) ≫ hB := rfl

/-- The diagram transitions are exactly the specified power-quotient maps. -/
theorem diagram_map_left (hB : Spec (.of B) ⟶ S) (I : Ideal B)
    {i j : ℕ} (f : i ⟶ j) :
    ((diagram hB I).map f).left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPow I
        (Nat.succ_le_succ (leOfHom f)))) := rfl

end AlgebraicGeometry.AdicPresentation
