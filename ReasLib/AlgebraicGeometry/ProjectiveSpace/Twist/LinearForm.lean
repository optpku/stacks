/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist.Coordinate
public import ReasLib.AlgebraicGeometry.Scheme.Module.Biproduct
public import Mathlib.Algebra.Field.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- The global section of `twistingSheaf k 2 1` associated to a homogeneous linear form. -/
noncomputable def sectionOfLinearForm {k : Type u} [Field k]
    (L : MvPolynomial (Fin (2 + 1)) k) (hL : L ∈ grading k 2 1) :
    (twistingSheaf k 2 1).sections :=
  RingedSpace.sectionFromTop (twistingSheaf k 2 1)
    (Proj.AssociatedModule.degreeZeroToGlobalSections (grading k 2)
      (GradedModule.shiftGrading
        (DirectSum.Decomposition.natToIntGrading (grading k 2)) (1 : ℤ))
      ⟨L, hL⟩)

/-- On a homogeneous coordinate, `sectionOfLinearForm` recovers `coordinateTwistSection`. -/
theorem sectionOfLinearForm_spec {k : Type u} [Field k] (i : Fin (2 + 1)) :
    sectionOfLinearForm (coordinate 2 i) (coordinate_mem_grading_one 2 i) =
      coordinateTwistSection k 2 i := sorry

/-- The morphism `𝒪 ⟶ 𝒪(1) ⊕ 𝒪(1) ⊕ 𝒪(1)` on `scheme k 2` with components the linear forms
`L i`. -/
noncomputable def linearFormHom {k : Type u} [Field k]
    (L : Fin (2 + 1) → MvPolynomial (Fin (2 + 1)) k)
    (hL : ∀ i, L i ∈ grading k 2 1) :
    (SheafOfModules.unit (scheme k 2).ringCatSheaf : (scheme k 2).Modules) ⟶
      biproduct (fun _ : Fin (2 + 1) ↦ twistingSheaf k 2 1) :=
  biproduct.lift fun i ↦
    (twistingSheaf k 2 1).unitHomEquiv.symm (sectionOfLinearForm (L i) (hL i))

/-- `linearFormHom` is the biproduct-lift of the unit maps associated to `sectionOfLinearForm`. -/
theorem linearFormHom_spec {k : Type u} [Field k]
    (L : Fin (2 + 1) → MvPolynomial (Fin (2 + 1)) k)
    (hL : ∀ i, L i ∈ grading k 2 1) :
    linearFormHom L hL =
      biproduct.lift fun i ↦
        (twistingSheaf k 2 1).unitHomEquiv.symm
          (sectionOfLinearForm (L i) (hL i)) := sorry

/-- The `i`-th component of `linearFormHom` is the unit map of `sectionOfLinearForm (L i)`. -/
theorem linearFormHom_π {k : Type u} [Field k]
    (L : Fin (2 + 1) → MvPolynomial (Fin (2 + 1)) k)
    (hL : ∀ i, L i ∈ grading k 2 1) (i : Fin (2 + 1)) :
    linearFormHom L hL ≫
        biproduct.π (fun _ : Fin (2 + 1) ↦ twistingSheaf k 2 1) i =
      (twistingSheaf k 2 1).unitHomEquiv.symm
        (sectionOfLinearForm (L i) (hL i)) := sorry

/-- The morphism `𝒪 ⟶ 𝒪(1) ⊕ 𝒪(1) ⊕ 𝒪(1)` on `scheme k 2` with components the homogeneous
coordinates `T i`. -/
noncomputable def coordinateLinearFormHom (k : Type u) [Field k] :
    (SheafOfModules.unit (scheme k 2).ringCatSheaf : (scheme k 2).Modules) ⟶
      biproduct (fun _ : Fin (2 + 1) ↦ twistingSheaf k 2 1) :=
  biproduct.lift fun i ↦
    (twistingSheaf k 2 1).unitHomEquiv.symm (coordinateTwistSection k 2 i)

/-- `coordinateLinearFormHom` is `linearFormHom` of the homogeneous coordinates. -/
theorem coordinateLinearFormHom_spec (k : Type u) [Field k] :
    coordinateLinearFormHom k =
      linearFormHom (fun i ↦ coordinate 2 i)
        (fun i ↦ coordinate_mem_grading_one 2 i) := sorry

/-- Three linear forms on `scheme k 2` are linearly independent if and only if they have no
common zero in the projective spectrum. -/
theorem linearIndependent_iff_zeroLocus_eq_empty {k : Type u} [Field k]
    (L : Fin (2 + 1) → MvPolynomial (Fin (2 + 1)) k)
    (hL : ∀ i, L i ∈ grading k 2 1) :
    LinearIndependent k L ↔
      ProjectiveSpectrum.zeroLocus (grading k 2) (Set.range L) = ∅ := sorry

end AlgebraicGeometry.ProjectiveSpace
