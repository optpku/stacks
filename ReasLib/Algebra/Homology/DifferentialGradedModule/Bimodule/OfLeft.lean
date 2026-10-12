/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Scalar
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.Endomorphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Left DG modules as DG bimodules over the base ring

A left differential graded `A`-module has a canonical commuting right action by the base ring.
This file packages that action as an `(A, R)`-DG bimodule, where `R` is regarded as a cochain
DGA concentrated in degree zero.  The construction is functorial and supplies the fixed
bimodule required by the existing derived tensor API.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open ComplexShape HomologicalComplex

namespace DifferentialGradedBimodule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, u} R}

/-- The right module over the degree-zero base DGA underlying a left DG `A`-module. -/
noncomputable abbrev ofLeftRightModule
    (N : LeftDifferentialGradedModule.{u, v} A) :
    DifferentialGradedModule.{u, v} (CochainDGAlgebra.ofAlgebra R R) :=
  (CochainDGAlgebra.Hom.fromBase A.opposite).restrictModule N.op

/-- The original left `A`-action, viewed as commuting with the canonical right base-ring
action. -/
noncomputable def ofLeftAction (N : LeftDifferentialGradedModule.{u, v} A) :
    LeftAction A (ofLeftRightModule N) where
  leftMul := N.smul
  left_assoc := sorry
  one_left := sorry
  comm_right := sorry
  d_leftMul := sorry

/-- On one homogeneous tensor summand, contract the ground-DGA factor into the
opposite algebra by its canonical scalar map. -/
@[stacks 0GZI "ground-factor contraction for base-valued bimodules"]
noncomputable def ofLeftEnvelopingComponent
    (A : CochainDGAlgebra.{u, u} R) (p q n : ℤ)
    (h : (up ℤ).π (up ℤ) (up ℤ) (p, q) = n) :
    ModuleCat.TensorProduct.obj R (A.opposite.X p)
        ((CochainDGAlgebra.ofAlgebra R R).X q) ⟶ A.opposite.X n :=
  ModuleCat.TensorProduct.map R (𝟙 (A.opposite.X p))
      ((CochainDGAlgebra.Hom.fromBase A.opposite).toCochainMap.f q) ≫
    CochainDGAlgebra.Tensor.mulHom A.opposite p q ≫
      eqToHom (congrArg A.opposite.X
        ((CochainDGAlgebra.Tensor.totalDegree p q).symm.trans h))

/-- The canonical DGA map `Aᵒᵖ ⊗[R] R ⟶ Aᵒᵖ` contracting the ground factor. -/
@[stacks 0GZI "ground-factor contraction of the enveloping DGA"]
noncomputable def ofLeftEnvelopingHom (A : CochainDGAlgebra.{u, u} R) :
    CochainDGAlgebra.Hom
      (CochainDGAlgebra.enveloping A (CochainDGAlgebra.ofAlgebra R R)) A.opposite where
  map n :=
    (mapBifunctorDesc (K₁ := A.opposite.toCochainComplex)
      (K₂ := (CochainDGAlgebra.ofAlgebra R R).toCochainComplex)
      (F := ModuleCat.TensorProduct.functor.{u, u, u} R) (c := up ℤ)
      (fun p q h ↦ ofLeftEnvelopingComponent A p q n h)).hom
  comm_d := sorry
  map_one := sorry
  map_mul := sorry

/-- A left DG `A`-module as the canonical differential graded `(A, R)`-bimodule. -/
@[stacks 0GZI "left differential graded modules as base-valued bimodules"]
noncomputable def ofLeft (N : LeftDifferentialGradedModule.{u, v} A) :
    DifferentialGradedBimodule.{u, v, u, u} A (CochainDGAlgebra.ofAlgebra R R) :=
  (ofLeftEnvelopingHom A).restrictModule N.op

/-- A morphism of left DG modules induces the corresponding morphism of base-valued DG
bimodules. -/
noncomputable def ofLeftHom {M N : LeftDifferentialGradedModule.{u, v} A}
    (f : M ⟶ N) : ofLeft M ⟶ ofLeft N :=
  (ofLeftEnvelopingHom A).restrictHom (LeftDifferentialGradedModule.Hom.op f)

/-- Packaging left DG modules as base-valued DG bimodules is functorial. -/
@[stacks 0GZI "left differential graded modules as base-valued bimodules"]
noncomputable def ofLeftFunctor (A : CochainDGAlgebra.{u, u} R) :
    LeftDifferentialGradedModule.{u, v} A ⥤
      DifferentialGradedBimodule.{u, v, u, u} A (CochainDGAlgebra.ofAlgebra R R) where
  obj := ofLeft
  map := ofLeftHom
  map_id := sorry
  map_comp := sorry

/-- The right module of `ofLeft N` is the base-ring restriction of the opposite module. -/
@[simp]
theorem ofLeft_toRightModule (N : LeftDifferentialGradedModule.{u, v} A) :
    (ofLeft N).toRightModule = ofLeftRightModule N := sorry

/-- Recovering the left module from `ofLeft N` returns `N`. -/
@[simp]
theorem ofLeft_toLeftModule (N : LeftDifferentialGradedModule.{u, v} A) :
    (ofLeft N).toLeftModule = N := sorry

/-- The bimodule map induced by a left-module map has the same homogeneous components. -/
@[simp]
theorem ofLeftHom_hom {M N : LeftDifferentialGradedModule.{u, v} A}
    (f : M ⟶ N) (n : ℤ) :
    (ofLeftHom f).hom n = f.hom n := sorry

end DifferentialGradedBimodule
