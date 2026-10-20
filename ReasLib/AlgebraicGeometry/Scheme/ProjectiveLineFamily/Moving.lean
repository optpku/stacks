/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveLineFamily
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.VectorSpace.ProjectiveEndomorphism.ProperIntersection

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLineFamily

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [Nontrivial V]

/-- A closed subvariety of projective space that properly intersects a second subvariety can be
placed in a dominant projective-line family with prescribed zero fiber and proper general fiber
intersections. -/
theorem existsMovingSubvariety
    {I : Type u} [Finite I]
    (N : ℕ) (hV : Module.finrank k V = N + 1)
    (X : SchemeOverField k) [Variety X]
    (iX : X ⟶ Over.mk (ProjectiveSpace.VectorSpace.toSpec k V))
    [IsClosedImmersion iX.left]
    (C : (ProjectiveSpace.VectorSpace.scheme k V).IdealSheafData)
    [Variety (Over.mk
      (C.subschemeι ≫ ProjectiveSpace.VectorSpace.toSpec k V))]
    (T : I → X.left.IdealSheafData)
    [∀ i, Variety (Over.mk ((T i).subschemeι ≫ X.hom))]
    (hproper : TopologicalSpace.Closeds.IntersectProperly C.support
      (iX.left.ker).support) :
    ∃ C' : (space (Over.mk
        (ProjectiveSpace.VectorSpace.toSpec k V))).IdealSheafData,
      Variety (Over.mk
        (C'.subschemeι ≫
          pullback.fst (ProjectiveSpace.VectorSpace.toSpec k V)
            (ProjectiveSpace.toBase 1 (Spec (CommRingCat.of k))) ≫
          ProjectiveSpace.VectorSpace.toSpec k V)) ∧
      IsDominant
        (C'.subschemeι ≫
          pullback.snd (ProjectiveSpace.VectorSpace.toSpec k V)
            (ProjectiveSpace.toBase 1 (Spec (CommRingCat.of k)))) ∧
      zeroImage (Over.mk (ProjectiveSpace.VectorSpace.toSpec k V)) C' = C ∧
      TopologicalSpace.Closeds.IntersectProperly C'.support
        (((iX.left.ker).comap
          (pullback.fst (ProjectiveSpace.VectorSpace.toSpec k V)
            (ProjectiveSpace.toBase 1 (Spec (CommRingCat.of k))))).support) ∧
      ∀ i, TopologicalSpace.Closeds.IntersectProperly
        (infinityImage
          (Over.mk (ProjectiveSpace.VectorSpace.toSpec k V)) C').support
        ((T i).map iX.left).support := sorry

end AlgebraicGeometry.ProjectiveLineFamily
