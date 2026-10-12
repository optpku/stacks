/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_5_6_Instances

/-!
# Derived tensor of quasi-coherent complexes on algebraic spaces

Fixed-right derived tensor preserves the full subcategory of `D(𝒪_X)` on complexes whose
cohomology sheaves are quasi-coherent, so `D_QCoh(𝒪_X)` is closed under `- ⊗^L -`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}}

namespace tensorRight

/-- Fixed-right derived tensor preserves derived modules with quasi-coherent cohomology. -/
theorem mapsTo {X : AlgebraicSpace S} (L : DerivedQCoh X) :
    derivedQuasiCoherentModuleProperty X ≤
      (derivedQuasiCoherentModuleProperty X).inverseImage
        (DerivedTensor.Right.functor L.obj) :=
  sorry

end tensorRight

/-- Fixed-right derived tensor `- ⊗^L L`, restricted to complexes with quasi-coherent
cohomology. -/
noncomputable def tensorRight {X : AlgebraicSpace S} (L : DerivedQCoh X) :
    DerivedQCoh X ⥤ DerivedQCoh X :=
  (derivedQuasiCoherentModuleProperty X).lift
    ((derivedQuasiCoherentModuleProperty X).ι ⋙ DerivedTensor.Right.functor L.obj)
    (fun K ↦ tensorRight.mapsTo L K.obj K.property)

/-- Forgetting the quasi-coherent lift of fixed-right derived tensor recovers ambient derived
tensor. -/
noncomputable def tensorRight.inclusionIso {X : AlgebraicSpace S} (L : DerivedQCoh X) :
    tensorRight L ⋙ (derivedQuasiCoherentModuleProperty X).ι ≅
      (derivedQuasiCoherentModuleProperty X).ι ⋙ DerivedTensor.Right.functor L.obj :=
  (derivedQuasiCoherentModuleProperty X).liftCompιIso
    ((derivedQuasiCoherentModuleProperty X).ι ⋙ DerivedTensor.Right.functor L.obj)
    (fun K ↦ tensorRight.mapsTo L K.obj K.property)

/-- The derived tensor product of two complexes with quasi-coherent cohomology. -/
noncomputable def tensorObj {X : AlgebraicSpace S} (K L : DerivedQCoh X) : DerivedQCoh X :=
  (tensorRight L).obj K

/-- The underlying derived module of a restricted tensor object is the ambient fixed-right
derived tensor. -/
@[simp]
theorem tensorObj_obj {X : AlgebraicSpace S} (K L : DerivedQCoh X) :
    (tensorObj K L).obj = (DerivedTensor.Right.functor L.obj).obj K.obj :=
  sorry

/-- The derived tensor product of two objects of `D_QCoh(𝒪_X)` again has quasi-coherent
cohomology. -/
theorem tensor_mem {X : AlgebraicSpace S} (K L : DerivedQCoh X) :
    derivedQuasiCoherentModuleProperty X
      ((DerivedTensor.Right.functor L.obj).obj K.obj) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
