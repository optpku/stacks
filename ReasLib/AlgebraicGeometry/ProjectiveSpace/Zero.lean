/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Coordinate

/-!
# Projective zero-space

The canonical structure morphism from projective zero-space over a commutative ring to the
spectrum of that ring is an isomorphism.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- The canonical structure morphism from projective zero-space over a commutative ring to its
affine base is an isomorphism. -/
instance toSpec_zero_isIso (A : Type u) [CommRing A] : IsIso (toSpec A 0) := by
  classical
  have hgen : Algebra.adjoin (grading A 0 0)
      (Set.range (MvPolynomial.X : Fin 1 → MvPolynomial (Fin 1) A)) = ⊤ := by
    refine top_unique fun p hp ↦ ?_
    clear hp
    induction p using MvPolynomial.induction_on with
    | C a => exact (Algebra.adjoin _ _).algebraMap_mem (degreeZeroC A 0 a)
    | add p q hp hq => exact add_mem hp hq
    | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)
  have hcover : Proj.basicOpen (grading A 0) (MvPolynomial.X (0 : Fin 1)) = ⊤ := by
    simpa using Proj.iSup_basicOpen_eq_top' (grading A 0)
      (MvPolynomial.X : Fin 1 → MvPolynomial (Fin 1) A)
      (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X A i⟩) hgen
  let e : coordinateAway (R := A) 0 0 ≃+* A :=
    (CoordinateChart.ringEquiv 0 0 (Equiv.refl (Fin 0))).trans
      (MvPolynomial.isEmptyRingEquiv A (Fin 0))
  have he : CommRingCat.ofHom (coefficientToCoordinateAway (R := A) 0 0) =
      e.toCommRingCatIso.inv := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change coefficientToCoordinateAway (R := A) 0 0 a =
      affineChartHom 0 0 (Equiv.refl (Fin 0))
        ((MvPolynomial.isEmptyRingEquiv A (Fin 0)).symm a)
    simp [affineChartHom]
  haveI : IsIso (CommRingCat.ofHom (coefficientToCoordinateAway (R := A) 0 0)) := by
    rw [he]
    infer_instance
  let j := Proj.awayι (grading A 0) (MvPolynomial.X (0 : Fin 1))
    (MvPolynomial.isHomogeneous_X A 0) Nat.zero_lt_one
  haveI : IsIso j := isIso_of_isOpenImmersion_of_opensRange_eq_top j (by
    rw [Proj.opensRange_awayι]
    exact hcover)
  have hj : j ≫ toSpec A 0 =
      Spec.map (CommRingCat.ofHom (coefficientToCoordinateAway (R := A) 0 0)) := by
    rw [toSpec, ← Category.assoc, Proj.awayι_toSpecZero]
    change Spec.map (CommRingCat.ofHom _) ≫
      Spec.map (CommRingCat.ofHom (degreeZeroRingEquiv A 0).symm.toRingHom) = _
    rw [← Spec.map_comp]
    rfl
  haveI : IsIso (j ≫ toSpec A 0) := by
    rw [hj]
    infer_instance
  exact IsIso.of_isIso_comp_left j (toSpec A 0)

end AlgebraicGeometry.ProjectiveSpace
