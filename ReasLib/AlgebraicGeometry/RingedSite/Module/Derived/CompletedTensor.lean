module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor.InternalHom
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Completion
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Completeness.InternalHom

/-! # Completed derived tensor products -/

@[expose] public section

open CategoryTheory SheafOfModules.RingedSite

noncomputable section

universe u

namespace RingedSite.Hom.ModuleDerived

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}

/-- The full subcategory of derived modules complete with respect to an ideal sheaf. -/
abbrev DerivedCompleteCategory (I : Subobject (unitModule J O)) :=
  (derivedCompleteObjectProperty.{u, u, u, u} I).FullSubcategory

/-- The completed tensor product is the derived completion of the derived tensor product. -/
abbrev completedTensorProduct (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (K L : DerivedCompleteCategory I) : DerivedCompleteCategory I :=
  (Completion.functor I).obj (Tensor.obj O K.obj L.obj)

/-- Derived tensor followed by completion is a bifunctor on complete derived modules. -/
def completedTensorProductFunctor (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType] :
    DerivedCompleteCategory I × DerivedCompleteCategory I ⥤ DerivedCompleteCategory I :=
  Functor.prod (derivedCompleteObjectProperty.{u, u, u, u} I).ι
      (derivedCompleteObjectProperty.{u, u, u, u} I).ι ⋙
    Tensor.functor O ⋙ Completion.functor I

/-- The completed tensor bifunctor evaluates to the completed tensor product of its arguments. -/
@[simp]
theorem completedTensorProductFunctor_obj (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (K L : DerivedCompleteCategory I) :
    (completedTensorProductFunctor I).obj (K, L) = completedTensorProduct I K L := rfl

/-- Derived sheaf internal Hom into a complete object is an object of the complete subcategory. -/
abbrev completedInternalHom (I : Subobject (unitModule J O))
    (L M : DerivedCompleteCategory I) : DerivedCompleteCategory I :=
  ⟨InternalHom.obj L.obj M.obj,
    internalHom_isDerivedComplete I L.obj M.obj M.property⟩

/-- The underlying derived object of complete internal Hom is derived sheaf internal Hom. -/
@[simp]
theorem completedInternalHom_obj (I : Subobject (unitModule J O))
    (L M : DerivedCompleteCategory I) :
    (completedInternalHom I L M).obj = InternalHom.obj L.obj M.obj := rfl

/-- Completed tensor and derived sheaf internal Hom satisfy the tensor–Hom equivalence
on complete derived modules. -/
def completedTensorProductHomEquiv (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (K L M : DerivedCompleteCategory I) :
    (K ⟶ completedInternalHom I L M) ≃ (completedTensorProduct I K L ⟶ M) :=
  (InducedCategory.homEquiv :
    (K ⟶ completedInternalHom I L M) ≃ (K.obj ⟶ InternalHom.obj L.obj M.obj)) |>.trans
    ((Tensor.homEquiv O K.obj L.obj M.obj).trans
      (Completion.homEquiv I (Tensor.obj O K.obj L.obj) M).symm)

end RingedSite.Hom.ModuleDerived
