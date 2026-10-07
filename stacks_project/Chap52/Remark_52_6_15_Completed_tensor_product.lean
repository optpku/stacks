module

public import stacks_project.Chap52.Proposition_52_6_12
public import stacks_project.Chap52.Lemma_52_6_5
public import ReasLib.CategoryTheory.Monoidal.Closed.Braided

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open SheafOfModules.RingedSite

noncomputable section

universe u v w z

namespace RingedSite.Hom.ModuleDerived

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}
variable [MonoidalCategory (RingedSiteDerived J O)]
variable [BraidedCategory (RingedSiteDerived J O)]

/-! The complete derived category is the full subcategory selected by the ideal sheaf. -/

/-- The category `D_comp(O)` of objects derived complete with respect to `I`. -/
abbrev DerivedCompleteCategory (I : Subobject (unitModule J O)) :=
  (derivedCompleteObjectProperty.{u, u, u, u} I).FullSubcategory

/-- The completion functor supplied by the left adjoint in Proposition 52.6.12. -/
noncomputable abbrev completionFunctor
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType] :
    RingedSiteDerived J O ⥤ DerivedCompleteCategory I :=
  Functor.leftAdjoint (derivedCompleteObjectProperty.{u, u, u, u} I).ι

/-- The chosen reflector adjunction used by the completed tensor-product hom-set equivalence. -/
noncomputable abbrev completionAdjunction
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType] :
    completionFunctor I ⊣ (derivedCompleteObjectProperty.{u, u, u, u} I).ι :=
  Adjunction.ofIsRightAdjoint (derivedCompleteObjectProperty.{u, u, u, u} I).ι

/-- Remark 52.6.15 (Completed tensor product) (1): the completed tensor product object in
`D_comp(O)` is the completion of the derived tensor product. -/
@[stacks 099G]
noncomputable abbrev completedTensorProduct
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (K L : DerivedCompleteCategory I) :
    DerivedCompleteCategory I :=
  (completionFunctor I).obj (K.obj ⊗ L.obj)

/-- Remark 52.6.15 (Completed tensor product) (2): completed tensoring is functorial in both
variables. -/
@[stacks 099G]
noncomputable def completedTensorProductFunctor
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType] :
    DerivedCompleteCategory I × DerivedCompleteCategory I ⥤ DerivedCompleteCategory I :=
  Functor.prod (derivedCompleteObjectProperty.{u, u, u, u} I).ι
      (derivedCompleteObjectProperty.{u, u, u, u} I).ι ⋙
    MonoidalCategory.tensor (RingedSiteDerived J O) ⋙
    completionFunctor I

/-- Evaluating the completed tensor-product bifunctor gives the named completed tensor object. -/
@[simp]
theorem completedTensorProductFunctor_obj
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (K L : DerivedCompleteCategory I) :
    (completedTensorProductFunctor I).obj (K, L) = completedTensorProduct I K L := sorry

/-- The derived internal Hom of complete objects, viewed in `D_comp(O)`. -/
noncomputable abbrev completedInternalHom
    (I : Subobject (unitModule J O))
    (H : MonoidalClosed (RingedSiteDerived J O))
    (L M : DerivedCompleteCategory I) :
    DerivedCompleteCategory I :=
  ⟨(ihomOf H L.obj).obj M.obj,
    internalHom_isDerivedComplete I H L.obj M.obj M.property⟩

/-- The ambient object underlying the complete internal Hom is the selected derived internal
Hom. -/
@[simp]
theorem completedInternalHom_obj
    (I : Subobject (unitModule J O))
    (H : MonoidalClosed (RingedSiteDerived J O))
    (L M : DerivedCompleteCategory I) :
    (completedInternalHom I H L M).obj = (ihomOf H L.obj).obj M.obj := sorry

/-- Remark 52.6.15 (Completed tensor product) (3): completed tensoring is left adjoint to the
derived internal Hom on `D_comp(O)`. -/
@[stacks 099G]
noncomputable def completedTensorProductHomEquiv
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (H : MonoidalClosed (RingedSiteDerived J O))
    (K L M : DerivedCompleteCategory I) :
    (K ⟶ completedInternalHom I H L M) ≃
      (completedTensorProduct I K L ⟶ M) :=
  Equiv.trans
    (InducedCategory.homEquiv :
      (K ⟶ completedInternalHom I H L M) ≃
        (K.obj ⟶ (completedInternalHom I H L M).obj))
    (Equiv.trans
      (((MonoidalClosed.adjunctionOf H L.obj).ofNatIsoLeft
        (BraidedCategory.tensorLeftIsoTensorRight L.obj)).homEquiv K.obj M.obj).symm
      ((completionAdjunction I).homEquiv (K.obj ⊗ L.obj) M).symm)

end RingedSite.Hom.ModuleDerived
