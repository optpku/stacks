module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.StructureSheaf
public import Mathlib.CategoryTheory.ObjectProperty.Shift

/-!
# Derived tensor of quasi-coherent complexes on algebraic spaces

Fixed-right derived tensor preserves the full subcategory of `D(𝒪_X)` on complexes whose
cohomology sheaves are quasi-coherent, so `D_QCoh(𝒪_X)` is closed under `- ⊗^L -`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory ObjectProperty

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
  rfl

/-- The derived tensor product of two objects of `D_QCoh(𝒪_X)` again has quasi-coherent
cohomology. -/
theorem tensor_mem {X : AlgebraicSpace S} (K L : DerivedQCoh X) :
    derivedQuasiCoherentModuleProperty X
      ((DerivedTensor.Right.functor L.obj).obj K.obj) :=
  tensorRight.mapsTo L K.obj K.property

/-- The restricted tensor object compares with the two-variable derived tensor bifunctor. -/
noncomputable def tensorObjIsoBifunctor {X : AlgebraicSpace S} (K L : DerivedQCoh X) :
    (tensorObj K L).obj ≅
      (DerivedTensor.Bifunctor.functor (C := Modules X)).obj (K.obj, L.obj) :=
  DerivedTensor.Bifunctor.Right.isoApp L.obj K.obj

/-- Functoriality of `tensorObj` in the right factor, via the two-variable derived tensor. -/
noncomputable def tensorMapRight {X : AlgebraicSpace S} (K : DerivedQCoh X)
    {L L' : DerivedQCoh X} (g : L ⟶ L') :
    tensorObj K L ⟶ tensorObj K L' :=
  ObjectProperty.homMk <|
    (tensorObjIsoBifunctor K L).hom ≫
      (DerivedTensor.Bifunctor.leftFunctor (C := Modules X) K.obj).map g.hom ≫
        (tensorObjIsoBifunctor K L').inv

/-- Degree-zero placement of the module tensor unit. -/
noncomputable def derivedTensorUnit (X : AlgebraicSpace S) : ModuleDerived X :=
  (DerivedCategory.singleFunctor (Modules X) 0).obj (tensorUnit (Modules X))

/-- The cochain-level right unitor `K ⊗ 𝟙 ⟶ K`, viewed in `D(𝒪_X)`. -/
noncomputable def derivedTensorRightUnitor {X : AlgebraicSpace S} (K : ModuleDerived X) :
    (DerivedTensor.Bifunctor.functor (C := Modules X)).obj (K, derivedTensorUnit X) ⟶ K :=
  (DerivedTensor.Bifunctor.functor (C := Modules X)).map
      (CategoryTheory.Prod.mkHom (DerivedCategory.Q.objObjPreimageIso K).inv
        (𝟙 (derivedTensorUnit X))) ≫
    DerivedTensor.Bifunctor.counitAppOfQ (DerivedCategory.Q.objPreimage K)
      (tensorUnit (CochainComplex (Modules X) ℤ)) ≫
    DerivedCategory.Q.map (MonoidalCategory.rightUnitor
      (DerivedCategory.Q.objPreimage K)).hom ≫
    (DerivedCategory.Q.objObjPreimageIso K).hom

/-- `derivedTensorRightUnitor` is the cochain right unitor transported to the derived category. -/
theorem derivedTensorRightUnitor_eq {X : AlgebraicSpace S} (K : ModuleDerived X) :
    derivedTensorRightUnitor K =
      (DerivedTensor.Bifunctor.functor (C := Modules X)).map
          (CategoryTheory.Prod.mkHom (DerivedCategory.Q.objObjPreimageIso K).inv
            (𝟙 (derivedTensorUnit X))) ≫
        DerivedTensor.Bifunctor.counitAppOfQ (DerivedCategory.Q.objPreimage K)
          (tensorUnit (CochainComplex (Modules X) ℤ)) ≫
        DerivedCategory.Q.map (MonoidalCategory.rightUnitor
          (DerivedCategory.Q.objPreimage K)).hom ≫
        (DerivedCategory.Q.objObjPreimageIso K).hom :=
  sorry

/-- The right unitor `K ⊗^L 𝒪_X ⟶ K` obtained by identifying the derived structure sheaf with
the degree-zero tensor unit and applying the cochain unitor. -/
noncomputable def tensorUnitor {X : AlgebraicSpace S} (K : DerivedQCoh X) :
    tensorObj K (structureSheaf X) ⟶ K :=
  ObjectProperty.homMk <|
    (tensorObjIsoBifunctor K (structureSheaf X)).hom ≫
      derivedTensorRightUnitor K.obj

/-- The underlying morphism of `tensorUnitor` is the cochain right unitor on the derived tensor
unit. -/
theorem tensorUnitor_eq {X : AlgebraicSpace S} (K : DerivedQCoh X) :
    (tensorUnitor K).hom =
      (tensorObjIsoBifunctor K (structureSheaf X)).hom ≫
        derivedTensorRightUnitor K.obj :=
  sorry

/-- Functoriality of `tensorObj` in both factors, via the two-variable derived tensor. -/
noncomputable def tensorMap {Z : AlgebraicSpace S} {K K' L L' : DerivedQCoh Z}
    (g : K ⟶ K') (h : L ⟶ L') :
    tensorObj K L ⟶ tensorObj K' L' :=
  ObjectProperty.homMk <|
    (tensorObjIsoBifunctor K L).hom ≫
      (DerivedTensor.Bifunctor.functor (C := Modules Z)).map (Prod.mkHom g.hom h.hom) ≫
        (tensorObjIsoBifunctor K' L').inv

/-- The underlying morphism of `tensorMap` is the two-variable derived tensor of the two
components. -/
theorem tensorMap_eq {Z : AlgebraicSpace S} {K K' L L' : DerivedQCoh Z}
    (g : K ⟶ K') (h : L ⟶ L') :
    (tensorMap g h).hom =
      (tensorObjIsoBifunctor K L).hom ≫
        (DerivedTensor.Bifunctor.functor (C := Modules Z)).map (Prod.mkHom g.hom h.hom) ≫
          (tensorObjIsoBifunctor K' L').inv :=
  sorry

/-- Restricted fixed-right derived tensor carries the ambient canonical shift. -/
noncomputable instance tensorRight.commShift {X : AlgebraicSpace S} (L : DerivedQCoh X) :
    (tensorRight L).CommShift ℤ :=
  inferInstanceAs (((derivedQuasiCoherentModuleProperty X).lift
    (inclusion X ⋙ DerivedTensor.Right.functor L.obj)
    (fun K ↦ tensorRight.mapsTo L K.obj K.property)).CommShift ℤ)

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
