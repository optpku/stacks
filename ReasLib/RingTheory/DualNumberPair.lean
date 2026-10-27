/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.DualNumber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/-- The commutative ring `DualNumberPair R` of a pair of square-zero directions over `R`. -/
abbrev DualNumberPair (R : Type u) : Type u :=
  TrivSqZeroExt R (R × R)

/-- The first square-zero generator of `DualNumberPair R`. -/
def DualNumberPair.eps1 {R : Type u} [CommRing R] : DualNumberPair R :=
  TrivSqZeroExt.inr (1, 0)

/-- The second square-zero generator of `DualNumberPair R`. -/
def DualNumberPair.eps2 {R : Type u} [CommRing R] : DualNumberPair R :=
  TrivSqZeroExt.inr (0, 1)

/-- The notation `ε₁` for the first square-zero generator. -/
scoped[DualNumberPair] notation "ε₁" => DualNumberPair.eps1

/-- The notation `ε₂` for the second square-zero generator. -/
scoped[DualNumberPair] notation "ε₂" => DualNumberPair.eps2

namespace DualNumberPair

variable (R : Type u) [CommRing R]

/-- The first square-zero generator has square zero. -/
theorem eps1_mul_eps1 : eps1 * eps1 = (0 : DualNumberPair R) := by
  exact TrivSqZeroExt.inr_mul_inr R _ _

/-- The second square-zero generator has square zero. -/
theorem eps2_mul_eps2 : eps2 * eps2 = (0 : DualNumberPair R) := by
  exact TrivSqZeroExt.inr_mul_inr R _ _

/-- The two square-zero generators have zero product. -/
theorem eps1_mul_eps2 : eps1 * eps2 = (0 : DualNumberPair R) := by
  exact TrivSqZeroExt.inr_mul_inr R _ _

/-- The algebra projection retaining the first square-zero direction. -/
def projFst : DualNumberPair R →ₐ[R] DualNumber R :=
  TrivSqZeroExt.map (LinearMap.fst R R R)

/-- The algebra projection retaining the second square-zero direction. -/
def projSnd : DualNumberPair R →ₐ[R] DualNumber R :=
  TrivSqZeroExt.map (LinearMap.snd R R R)

/-- The first projection maps `ε₁` to the dual-number generator. -/
theorem projFst_eps1 : projFst R eps1 = DualNumber.eps := by
  exact TrivSqZeroExt.map_inr _ _

/-- The first projection maps `ε₂` to zero. -/
theorem projFst_eps2 : projFst R eps2 = 0 := by
  simp [projFst, eps2]

/-- The second projection maps `ε₁` to zero. -/
theorem projSnd_eps1 : projSnd R eps1 = 0 := by
  simp [projSnd, eps1]

/-- The second projection maps `ε₂` to the dual-number generator. -/
theorem projSnd_eps2 : projSnd R eps2 = DualNumber.eps := by
  exact TrivSqZeroExt.map_inr _ _

/-- The square of coordinate rings defined by the two projections is a pullback. -/
theorem isPullback :
    IsPullback
      (CommRingCat.ofHom (projFst R).toRingHom)
      (CommRingCat.ofHom (projSnd R).toRingHom)
      (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom)
      (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  let f := CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom
  have compat (s : Limits.PullbackCone f f) (x : s.pt) :
      (s.fst x).fst = (s.snd x).fst :=
    congrArg (fun k : s.pt ⟶ CommRingCat.of R ↦ k x) s.condition
  let lift (s : Limits.PullbackCone f f) : s.pt ⟶ CommRingCat.of (DualNumberPair R) :=
    CommRingCat.ofHom
      { toFun x := ((s.fst x).fst, ((s.fst x).snd, (s.snd x).snd))
        map_one' := by
          ext <;> simp
        map_mul' := by
          intro x y
          apply TrivSqZeroExt.ext
          · change (s.fst (x * y)).fst = (s.fst x).fst * (s.fst y).fst
            simp
          · apply Prod.ext
            · change (s.fst (x * y)).snd =
                (s.fst x).fst * (s.fst y).snd + (s.fst x).snd * (s.fst y).fst
              simp
            · change (s.snd (x * y)).snd =
                (s.fst x).fst * (s.snd y).snd + (s.snd x).snd * (s.fst y).fst
              simp [compat s x, compat s y]
        map_zero' := by
          ext <;> simp
        map_add' := by
          intro x y
          ext <;> simp }
  have w : CommRingCat.ofHom (projFst R).toRingHom ≫ f =
      CommRingCat.ofHom (projSnd R).toRingHom ≫ f := by
    ext x
    simp [f, projFst, projSnd]
  refine { w := w, isLimit' := ⟨Limits.PullbackCone.IsLimit.mk w lift ?_ ?_ ?_⟩ }
  · intro s
    ext x <;> simp [lift, projFst]
  · intro s
    ext x <;> simp [lift, projSnd, compat]
  · intro s m hfst hsnd
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    have h₁ := congrArg (fun k : s.pt ⟶ CommRingCat.of (DualNumber R) ↦ k x) hfst
    have h₂ := congrArg (fun k : s.pt ⟶ CommRingCat.of (DualNumber R) ↦ k x) hsnd
    apply TrivSqZeroExt.ext
    · simpa [lift, projFst] using congrArg TrivSqZeroExt.fst h₁
    · apply Prod.ext
      · simpa [lift, projFst] using congrArg TrivSqZeroExt.snd h₁
      · simpa [lift, projSnd] using congrArg TrivSqZeroExt.snd h₂

/-- The `R`-algebra homomorphism `DualNumberPair R →ₐ[R] DualNumber R` sending
`ε₁` and `ε₂` to `ε`. -/
def sumAlgHom : DualNumberPair R →ₐ[R] DualNumber R :=
  TrivSqZeroExt.map (LinearMap.fst R R R + LinearMap.snd R R R)

/-- The sum algebra homomorphism sends the first square-zero generator to `ε`. -/
theorem sumAlgHom_eps1 : sumAlgHom R eps1 = DualNumber.eps := by
  rw [sumAlgHom, eps1, TrivSqZeroExt.map_inr]
  exact congrArg TrivSqZeroExt.inr (add_zero (1 : R))

/-- The sum algebra homomorphism sends the second square-zero generator to `ε`. -/
theorem sumAlgHom_eps2 : sumAlgHom R eps2 = DualNumber.eps := by
  rw [sumAlgHom, eps2, TrivSqZeroExt.map_inr]
  exact congrArg TrivSqZeroExt.inr (zero_add (1 : R))

noncomputable section

/-- The scheme morphism induced by `sumAlgHom`, from the dual-number spectrum
to the spectrum of the pair of square-zero directions. -/
def sum :
    Spec (CommRingCat.of (DualNumber R)) ⟶ Spec (CommRingCat.of (DualNumberPair R)) :=
  Spec.map (CommRingCat.ofHom (sumAlgHom R).toRingHom)

end

end DualNumberPair
