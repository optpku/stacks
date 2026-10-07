module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ProjectionFormula
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Tensor.Right
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ProjectionFormula.KFlatModel
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Dualizable

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The canonical comparison from the fixed-right tensor model underlying `tensorObj` to the
monoidal derived tensor product. -/
noncomputable abbrev tensorObjIsoTensor {X : Scheme.{u}}
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    (K L : DerivedQCoh X) :
    (tensorObj K L).obj ≅ K.obj ⊗ L.obj :=
  @DerivedCategory.DerivedTensor.Right.Monoidal.Model.objIsoTensor
    (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _ _
    (RingedSpace.ModuleDerived.monoidalCategory X.toRingedSpace)
    (@ModuleDerived.ProjectionFormula.kFlatTensorModel X
      (ModuleDerived.ProjectionFormula.hasKFlatResolutions X)
      (inferInstanceAs (HomotopyTensorDescends X.toRingedSpace))
      (inferInstanceAs (TensorDescends X.toRingedSpace))
      (inferInstanceAs (TensorDescends X.toRingedSpace))
      (inferInstanceAs (IsLocalization X.toRingedSpace))
      (inferInstanceAs (IsLocalization X.toRingedSpace))
      (ModuleDerived.ProjectionFormula.homotopyLocalization_isLocalization X))
    K.obj L.obj _

/-- The derived structure sheaf is canonically the tensor unit. -/
noncomputable def structureSheafUnitIso (X : Scheme.{u})
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace] :
    (structureSheaf X).obj ≅ 𝟙_ (RingedSpace.ModuleDerived X.toRingedSpace) :=
  eqToIso (structureSheaf_obj X) ≪≫
    (DerivedCategory.singleFunctor X.Modules 0).mapIso
      (RingedSpace.unitIsoTensorUnit X.toRingedSpace) ≪≫
    (DerivedCategory.KFlat.mapUnitIso
      (C := RingedSpace.Modules X.toRingedSpace)).symm

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [QuasiCompact f] [QuasiSeparated f]
variable [HomotopyTensorDescends X.toRingedSpace]
variable [TensorDescends X.toRingedSpace]
variable [IsLocalization X.toRingedSpace]
variable [HomotopyTensorDescends Y.toRingedSpace]
variable [TensorDescends Y.toRingedSpace]
variable [IsLocalization Y.toRingedSpace]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom f.toShHom)]
variable [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]

/-- The canonical projection-formula isomorphism after restricting both sides to derived
modules with quasicoherent cohomology. -/
noncomputable def projectionFormulaIso (K : DerivedQCoh Y) (E : DerivedQCoh X) :
    (pushforwardCohomologyIn f).obj (tensorObj ((pullback f).obj K) E) ≅
      tensorObj K ((pushforwardCohomologyIn f).obj E) :=
  (ModuleDerived.quasicoherentProperty Y).fullyFaithfulι.preimageIso
    ((pushforwardCohomologyIn.inclusionIso f).app
        (tensorObj ((pullback f).obj K) E) ≪≫
      (RingedSpace.moduleDerivedPushforward f.toShHom).mapIso
        (tensorObjIsoTensor ((pullback f).obj K) E) ≪≫
      (RingedSpace.moduleDerivedPushforward f.toShHom).mapIso
        (((pullback.inclusionIso f).app K) ⊗ᵢ Iso.refl E.obj) ≪≫
      (RingedSpace.moduleDerivedPushforward f.toShHom).mapIso
        (β_ ((RingedSpace.modulePullbackDerived f.toShHom).obj K.obj) E.obj) ≪≫
      (@asIso _ _ _ _
        (RingedSpace.ModuleDerived.ProjectionFormula.leftMate f.toShHom E.obj K.obj)
        (isIso_projectionFormula f E K)).symm ≪≫
      β_ ((RingedSpace.moduleDerivedPushforward f.toShHom).obj E.obj) K.obj ≪≫
      (Iso.refl K.obj ⊗ᵢ
        ((pushforwardCohomologyIn.inclusionIso f).app E).symm) ≪≫
      (tensorObjIsoTensor K ((pushforwardCohomologyIn f).obj E)).symm)

/-- The underlying map of `projectionFormulaIso` is the canonical inverse
projection-formula composite with the inclusion and tensor comparisons. -/
theorem projectionFormulaIso_hom (K : DerivedQCoh Y) (E : DerivedQCoh X) :
    (projectionFormulaIso f K E).hom.hom =
      ((pushforwardCohomologyIn.inclusionIso f).app
          (tensorObj ((pullback f).obj K) E) ≪≫
        (RingedSpace.moduleDerivedPushforward f.toShHom).mapIso
          (tensorObjIsoTensor ((pullback f).obj K) E) ≪≫
        (RingedSpace.moduleDerivedPushforward f.toShHom).mapIso
          (((pullback.inclusionIso f).app K) ⊗ᵢ Iso.refl E.obj) ≪≫
        (RingedSpace.moduleDerivedPushforward f.toShHom).mapIso
          (β_ ((RingedSpace.modulePullbackDerived f.toShHom).obj K.obj) E.obj) ≪≫
        (@asIso _ _ _ _
          (RingedSpace.ModuleDerived.ProjectionFormula.leftMate f.toShHom E.obj K.obj)
          (isIso_projectionFormula f E K)).symm ≪≫
        β_ ((RingedSpace.moduleDerivedPushforward f.toShHom).obj E.obj) K.obj ≪≫
        (Iso.refl K.obj ⊗ᵢ
          ((pushforwardCohomologyIn.inclusionIso f).app E).symm) ≪≫
        (tensorObjIsoTensor K ((pushforwardCohomologyIn f).obj E)).symm).hom := sorry

/-- Tensor the counit `Rf_* a(L) ⟶ L` with `K` in `DerivedQCoh Y`. -/
noncomputable def tensorCounitMap
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K L : DerivedQCoh Y) :
    tensorObj K ((pushforwardCohomologyIn f).obj (a.obj L)) ⟶ tensorObj K L :=
  ⟨(tensorObjIsoTensor K ((pushforwardCohomologyIn f).obj (a.obj L))).hom ≫
    (𝟙 K.obj ⊗ₘ (aAdjunction.counit.app L).hom) ≫
    (tensorObjIsoTensor K L).inv⟩

/-- The underlying morphism of `tensorCounitMap` is the tensor of the adjunction counit. -/
theorem tensorCounitMap_spec
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K L : DerivedQCoh Y) :
    (tensorCounitMap f a aAdjunction K L).hom =
      (tensorObjIsoTensor K ((pushforwardCohomologyIn f).obj (a.obj L))).hom ≫
        (𝟙 K.obj ⊗ₘ (aAdjunction.counit.app L).hom) ≫
        (tensorObjIsoTensor K L).inv := sorry

/-- Specializing the tensor of the counit to `𝒪_Y` and applying the right unitor gives
`K ⊗ᴸ Rf_* a(𝒪_Y) ⟶ K`. -/
noncomputable def tensorCounitToUnit
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K : DerivedQCoh Y) :
    tensorObj K ((pushforwardCohomologyIn f).obj (a.obj (structureSheaf Y))) ⟶ K :=
  tensorCounitMap f a aAdjunction K (structureSheaf Y) ≫
    ⟨(tensorObjIsoTensor K (structureSheaf Y)).hom ≫
      (𝟙 K.obj ⊗ₘ (structureSheafUnitIso Y).hom) ≫ (ρ_ K.obj).hom⟩

/-- `tensorCounitToUnit` is the counit tensor map followed by the canonical structure-sheaf
and right-unitor comparison. -/
theorem tensorCounitToUnit_spec
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K : DerivedQCoh Y) :
    tensorCounitToUnit f a aAdjunction K =
      tensorCounitMap f a aAdjunction K (structureSheaf Y) ≫
        ⟨(tensorObjIsoTensor K (structureSheaf Y)).hom ≫
          (𝟙 K.obj ⊗ₘ (structureSheafUnitIso Y).hom) ≫ (ρ_ K.obj).hom⟩ := sorry

/-- The projection-formula and counit map
`Lf^*K ⊗ᴸ a(L) ⟶ a(K ⊗ᴸ L)` for a chosen right adjoint `a` to `Rf_*`. -/
noncomputable def pullbackTensorRightAdjointMap
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K L : DerivedQCoh Y) :
    tensorObj ((pullback f).obj K) (a.obj L) ⟶ a.obj (tensorObj K L) :=
  aAdjunction.homEquiv _ _
    ((projectionFormulaIso f K (a.obj L)).hom ≫ tensorCounitMap f a aAdjunction K L)

/-- Transposing `pullbackTensorRightAdjointMap` recovers the projection-formula isomorphism
followed by the tensor of the counit. -/
theorem pullbackTensorRightAdjointMap_spec
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K L : DerivedQCoh Y) :
    (aAdjunction.homEquiv _ _).symm (pullbackTensorRightAdjointMap f a aAdjunction K L) =
      (projectionFormulaIso f K (a.obj L)).hom ≫
        tensorCounitMap f a aAdjunction K L := sorry

/-- The canonical comparison `Lf^*K ⊗ᴸ a(𝒪_Y) ⟶ a(K)` obtained from projection formula
and the counit of `Rf_* ⊣ a`. -/
noncomputable def pullbackTensorDualityMap
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K : DerivedQCoh Y) :
    tensorObj ((pullback f).obj K) (a.obj (structureSheaf Y)) ⟶ a.obj K :=
  aAdjunction.homEquiv _ _
    ((projectionFormulaIso f K (a.obj (structureSheaf Y))).hom ≫
      tensorCounitToUnit f a aAdjunction K)

/-- Transposing `pullbackTensorDualityMap` recovers projection formula followed by the
counit-to-unit map. -/
theorem pullbackTensorDualityMap_spec
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K : DerivedQCoh Y) :
    (aAdjunction.homEquiv _ _).symm (pullbackTensorDualityMap f a aAdjunction K) =
      (projectionFormulaIso f K (a.obj (structureSheaf Y))).hom ≫
        tensorCounitToUnit f a aAdjunction K := sorry

/-- The duality comparison is natural in `K`. -/
theorem pullbackTensorDualityMap_naturality
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    {K K' : DerivedQCoh Y} (g : K ⟶ K') :
    (pullback f ⋙ tensorRight (a.obj (structureSheaf Y))).map g ≫
        pullbackTensorDualityMap f a aAdjunction K' =
      pullbackTensorDualityMap f a aAdjunction K ≫ a.map g := sorry

/-- The canonical duality comparisons, packaged as a natural transformation in `K`. -/
noncomputable def pullbackTensorDualityNatTrans
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a) :
    pullback f ⋙ tensorRight (a.obj (structureSheaf Y)) ⟶ a where
  app K := pullbackTensorDualityMap f a aAdjunction K
  naturality _ _ g := pullbackTensorDualityMap_naturality f a aAdjunction g

/-- The component of `pullbackTensorDualityNatTrans` is `pullbackTensorDualityMap`. -/
theorem pullbackTensorDualityNatTrans_app
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K : DerivedQCoh Y) :
    (pullbackTensorDualityNatTrans f a aAdjunction).app K =
      pullbackTensorDualityMap f a aAdjunction K := sorry

/-- The comparison map `Lf^*K ⊗ᴸ a(L) ⟶ a(K ⊗ᴸ L)` is invertible when `K` is perfect. -/
theorem pullbackTensorRightAdjointMap_isIso_of_isPerfect
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K L : DerivedQCoh Y) (hK : RingedSpace.ModuleDerived.IsPerfect K.obj) :
    IsIso (pullbackTensorRightAdjointMap f a aAdjunction K L) := sorry

/-- The structure-sheaf specialization `Lf^*K ⊗ᴸ a(𝒪_Y) ⟶ a(K)` is invertible when `K` is
perfect. -/
theorem pullbackTensorDualityMap_isIso_of_isPerfect
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K : DerivedQCoh Y) (hK : RingedSpace.ModuleDerived.IsPerfect K.obj) :
    IsIso (pullbackTensorDualityMap f a aAdjunction K) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
