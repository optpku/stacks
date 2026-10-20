module

public import ReasLib.Algebra.Category.Grp.ULiftIntModule
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CompactSupport.Compactification
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Comparison of compactly supported global sections and derived cohomology

The canonical comparison factors through global sections of extension by zero
on a compactification, coefficient conversion, and degree-zero derived cohomology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section CoefficientSheaf

variable {Y : Scheme.{u}}
variable [Y.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toULiftIntModule]

/-- The sheaf of `ULift ℤ`-modules associated to an abelian small-étale sheaf. -/
def etaleAbelianToIntModuleSheaf
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)) :=
  (sheafCompose Y.smallEtaleTopology AddCommGrpCat.toULiftIntModule).obj F

/-- The associated module sheaf is obtained by composing its coefficients with the lifted-
integer functor. -/
theorem etaleAbelianToIntModuleSheaf_obj
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleAbelianToIntModuleSheaf F =
      (sheafCompose Y.smallEtaleTopology AddCommGrpCat.toULiftIntModule).obj F :=
  sorry

end CoefficientSheaf

variable {k : Type u} [Field k]
variable {X : SchemeOverField k}
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)
variable [IsOpenImmersion (Compactification.Of.ι P)]
variable [IsProper P.obj.right.hom]

variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} (ULift.{u} ℤ))]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} (ULift.{u} ℤ))]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))]
variable [HasSheafify (Spec (CommRingCat.of k)).smallEtaleTopology
  (ModuleCat.{u} (ULift.{u} ℤ))]
variable [∀ U : (Spec (CommRingCat.of k)).Etale,
  HasWeakSheafify ((Spec (CommRingCat.of k)).smallEtaleTopology.over U)
    (ModuleCat.{u} (ULift.{u} ℤ))]
variable [HasDerivedCategory
  (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} (ULift.{u} ℤ),
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} (ULift.{u} ℤ))).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} (ULift.{u} ℤ)))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} (ULift.{u} ℤ)))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} (ULift.{u} ℤ)) (Spec (CommRingCat.of k)).smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} (ULift.{u} ℤ)) (Spec (CommRingCat.of k)).smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))
    (ComplexShape.up ℤ))]
variable [HasDerivedCategory (ModuleCat.{u} (ULift.{u} ℤ))]
variable [((sheafSections (Spec (CommRingCat.of k)).smallEtaleTopology
    (ModuleCat.{u} (ULift.{u} ℤ))).obj
    (op (globalEtale (Spec (CommRingCat.of k))))).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((sheafSections (Spec (CommRingCat.of k)).smallEtaleTopology
        (ModuleCat.{u} (ULift.{u} ℤ))).obj
      (op (globalEtale (Spec (CommRingCat.of k))))))
  (HomologicalComplex.quasiIso
    (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))
    (ComplexShape.up ℤ))]
variable [CompactSpace (Spec (CommRingCat.of k))]
variable [QuasiSeparatedSpace (Spec (CommRingCat.of k))]
variable [HasWeakSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [∀ G : P.obj.right.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (Compactification.Of.ι P)).op.HasLeftKanExtension G]
variable [((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous
    AddCommGrpCat.{u} P.obj.right.left.smallEtaleTopology
    X.left.smallEtaleTopology).IsRightAdjoint]
variable [X.left.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toULiftIntModule]
variable [P.obj.right.left.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toULiftIntModule]
variable [X.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u})]
variable [P.obj.right.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u})]

/-- Pullback of global sections of `j_! F` along `globalEtalePullbackIso` of the
compactification structure map. -/
def etaleExtensionByZeroGlobalSectionsPullback
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))) :
    ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} (ULift.{u} ℤ))).obj F).obj.obj
        (op (globalEtale P.obj.right.left)) ⟶
      (((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
            (ModuleCat.{u} (ULift.{u} ℤ))
            (Spec (CommRingCat.of k)).smallEtaleTopology
            P.obj.right.left.smallEtaleTopology).obj
          ((etaleExtensionByZero (Compactification.Of.ι P)
              (ModuleCat.{u} (ULift.{u} ℤ))).obj F)).obj.obj
        (op (globalEtale (Spec (CommRingCat.of k)))) :=
  ((etaleExtensionByZero (Compactification.Of.ι P)
        (ModuleCat.{u} (ULift.{u} ℤ))).obj F).obj.map
    (op (globalEtalePullbackIso P.obj.right.hom).hom)

/-- Pullback of global sections is evaluation on the canonical identification of the pulled-back
terminal étale object. -/
theorem etaleExtensionByZeroGlobalSectionsPullback_eq
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))) :
    etaleExtensionByZeroGlobalSectionsPullback P F =
      ((etaleExtensionByZero (Compactification.Of.ι P)
            (ModuleCat.{u} (ULift.{u} ℤ))).obj F).obj.map
        (op (globalEtalePullbackIso P.obj.right.hom).hom) :=
  sorry

/-- The comparison morphism in `D(ULift ℤ)` from the single complex on
`Γ(X̄, j_! F)` to `RΓ_c(X, F[0])`. -/
def etaleDerivedCohomologyCompactSupportFromDerived
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))) :
    (DerivedCategory.singleFunctor (ModuleCat.{u} (ULift.{u} ℤ)) (0 : ℤ)).obj
      (((etaleExtensionByZero (Compactification.Of.ι P)
            (ModuleCat.{u} (ULift.{u} ℤ))).obj F).obj.obj
        (op (globalEtale P.obj.right.left))) ⟶
      (etaleDerivedGammaCompactSupport P).obj
        ((DerivedCategory.singleFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))
            (0 : ℤ)).obj F) :=
  let π := P.obj.right.hom
  let ext0 := etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} (ULift.{u} ℤ))
  let G := ext0.obj F
  let push :=
    (smallEtalePullback π).sheafPushforwardContinuous (ModuleCat.{u} (ULift.{u} ℤ))
      (Spec (CommRingCat.of k)).smallEtaleTopology
      P.obj.right.left.smallEtaleTopology
  let Γk :=
    (sheafSections (Spec (CommRingCat.of k)).smallEtaleTopology
        (ModuleCat.{u} (ULift.{u} ℤ))).obj
      (op (globalEtale (Spec (CommRingCat.of k))))
  (DerivedCategory.singleFunctor (ModuleCat.{u} (ULift.{u} ℤ)) (0 : ℤ)).map
      (etaleExtensionByZeroGlobalSectionsPullback P F) ≫
    (DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex Γk
              (ComplexShape.up ℤ) (0 : ℤ)).inv.app (push.obj G)) ≫
      (RightDerived.Cochain.unit Γk).app
        ((HomologicalComplex.single
            (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology
              (ModuleCat.{u} (ULift.{u} ℤ)))
            (ComplexShape.up ℤ) (0 : ℤ)).obj (push.obj G))) ≫
      (etaleDerivedGamma (Spec (CommRingCat.of k)) (ULift.{u} ℤ)).map
          (DerivedCategory.Q.map
              ((HomologicalComplex.singleMapHomologicalComplex push
                    (ComplexShape.up ℤ) (0 : ℤ)).inv.app G) ≫
            (RightDerived.Cochain.unit push).app
              ((HomologicalComplex.single
                  (Sheaf P.obj.right.left.smallEtaleTopology
                    (ModuleCat.{u} (ULift.{u} ℤ)))
                  (ComplexShape.up ℤ) (0 : ℤ)).obj G)) ≫
        (etaleDerivedGamma (Spec (CommRingCat.of k)) (ULift.{u} ℤ)).map
          ((etaleDerivedPushforward π).map
            ((ext0.mapDerivedCategorySingleFunctor (0 : ℤ)).inv.app F))

/-- The `ModuleCat` comparison `Γ(X̄, j_! F) ⟶ H^0_c(X, F[0])`. -/
def etaleDerivedCohomologyCompactSupportFromGlobal
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))) :
    ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} (ULift.{u} ℤ))).obj F).obj.obj
        (op (globalEtale P.obj.right.left)) ⟶
      etaleDerivedCohomologyCompactSupport P 0
        ((DerivedCategory.singleFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))
            (0 : ℤ)).obj F) :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{u} (ULift.{u} ℤ)) (0 : ℤ)).inv.app
      (((etaleExtensionByZero (Compactification.Of.ι P)
            (ModuleCat.{u} (ULift.{u} ℤ))).obj F).obj.obj
        (op (globalEtale P.obj.right.left))) ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (ULift.{u} ℤ)) (0 : ℤ)).map
      (etaleDerivedCohomologyCompactSupportFromDerived P F)

/-- The comparison on global sections is degree-zero homology of the derived comparison after
the single-functor identification. -/
theorem etaleDerivedCohomologyCompactSupportFromGlobal_comp
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))) :
    etaleDerivedCohomologyCompactSupportFromGlobal P F =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
              (ModuleCat.{u} (ULift.{u} ℤ)) (0 : ℤ)).inv.app
          (((etaleExtensionByZero (Compactification.Of.ι P)
                (ModuleCat.{u} (ULift.{u} ℤ))).obj F).obj.obj
            (op (globalEtale P.obj.right.left))) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (ULift.{u} ℤ)) (0 : ℤ)).map
          (etaleDerivedCohomologyCompactSupportFromDerived P F) :=
  sorry

/-- The degree-zero derived comparison on global sections, viewed as an additive homomorphism. -/
def etaleDerivedCohomologyCompactSupportZeroAddHom
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))) :
    ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} (ULift.{u} ℤ))).obj F).obj.obj
        (op (globalEtale P.obj.right.left)) →+
      etaleDerivedCohomologyCompactSupport P 0
        ((DerivedCategory.singleFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))
            (0 : ℤ)).obj F) :=
  (etaleDerivedCohomologyCompactSupportFromGlobal P F).hom.toAddMonoidHom

/-- The additive degree-zero comparison is the underlying additive map of the module comparison. -/
theorem etaleDerivedCohomologyCompactSupportZeroAddHom_eq
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))) :
    etaleDerivedCohomologyCompactSupportZeroAddHom P F =
      (etaleDerivedCohomologyCompactSupportFromGlobal P F).hom.toAddMonoidHom :=
  sorry

/-- The additive comparison `Γ(X̄, j_! F) →+ H^0_c(X, F[0])` is bijective. -/
theorem etaleDerivedCohomologyCompactSupportZero_bijective
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))
    (hF :
      IsLocallyTorsion
        ((sheafCompose X.left.smallEtaleTopology
            (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u})).obj F)) :
    Function.Bijective (etaleDerivedCohomologyCompactSupportZeroAddHom P F) :=
  sorry

/-- Additive equivalence `Γ(X̄, j_! F) ≃+ derived H^0_c(X, F[0])`. -/
def etaleDerivedCohomologyCompactSupportZeroEquiv
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))
    (hF :
      IsLocallyTorsion
        ((sheafCompose X.left.smallEtaleTopology
            (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u})).obj F)) :
    ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} (ULift.{u} ℤ))).obj F).obj.obj
        (op (globalEtale P.obj.right.left)) ≃+
      etaleDerivedCohomologyCompactSupport P 0
        ((DerivedCategory.singleFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))
            (0 : ℤ)).obj F) :=
  { toFun := etaleDerivedCohomologyCompactSupportZeroAddHom P F
    invFun := Function.invFun (etaleDerivedCohomologyCompactSupportZeroAddHom P F)
    left_inv := Function.leftInverse_invFun (etaleDerivedCohomologyCompactSupportZero_bijective P F hF).injective
    right_inv := Function.rightInverse_invFun (etaleDerivedCohomologyCompactSupportZero_bijective P F hF).surjective
    map_add' := (etaleDerivedCohomologyCompactSupportZeroAddHom P F).map_add }

/-- The degree-zero comparison equivalence acts by the canonical additive comparison on global
sections. -/
theorem etaleDerivedCohomologyCompactSupportZeroEquiv_apply
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))
    (hF :
      IsLocallyTorsion
        ((sheafCompose X.left.smallEtaleTopology
            (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u})).obj F))
    (σ :
      ((etaleExtensionByZero (Compactification.Of.ι P)
            (ModuleCat.{u} (ULift.{u} ℤ))).obj F).obj.obj
        (op (globalEtale P.obj.right.left))) :
    etaleDerivedCohomologyCompactSupportZeroEquiv P F hF σ =
      etaleDerivedCohomologyCompactSupportZeroAddHom P F σ :=
  sorry

/-- Restriction along the interior immersion commutes with conversion from
abelian coefficients to `ULift ℤ`-modules. -/
def etaleRestrictionSheafComposeConverter :
    TwoSquare
      (etaleRestrictionSheaf (Compactification.Of.ι P) AddCommGrpCat.{u})
      (sheafCompose P.obj.right.left.smallEtaleTopology AddCommGrpCat.toULiftIntModule)
      (sheafCompose X.left.smallEtaleTopology AddCommGrpCat.toULiftIntModule)
      (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} (ULift.{u} ℤ))) :=
  (𝟙
    (etaleRestrictionSheaf (Compactification.Of.ι P) AddCommGrpCat.{u} ⋙
      sheafCompose X.left.smallEtaleTopology AddCommGrpCat.toULiftIntModule))

/-- The adjunction mate of the restriction square compares extension by zero after coefficient
conversion with coefficient conversion after extension by zero. -/
def etaleExtensionByZeroConverter :
    TwoSquare
      (sheafCompose X.left.smallEtaleTopology AddCommGrpCat.toULiftIntModule)
      (abelianExtensionByZero (Compactification.Of.ι P))
      (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} (ULift.{u} ℤ)))
      (sheafCompose P.obj.right.left.smallEtaleTopology AddCommGrpCat.toULiftIntModule) :=
  (mateEquiv
      (abelianExtensionByZero_adjunction (Compactification.Of.ι P))
      (etaleExtensionByZero_adjunction (Compactification.Of.ι P)
        (ModuleCat.{u} (ULift.{u} ℤ)))).symm
    (etaleRestrictionSheafComposeConverter P)

/-- Global sections of the mate comparing `j_! F_ℤ` with the coefficient
conversion of `j_! F`. -/
def etaleExtensionByZeroConverterSections
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} (ULift.{u} ℤ))).obj
        (etaleAbelianToIntModuleSheaf F)).obj.obj
        (op (globalEtale P.obj.right.left)) →+
      ((sheafCompose P.obj.right.left.smallEtaleTopology
            AddCommGrpCat.toULiftIntModule).obj
        ((abelianExtensionByZero (Compactification.Of.ι P)).obj F)).obj.obj
        (op (globalEtale P.obj.right.left)) :=
  (((etaleExtensionByZeroConverter P).app F).hom.app
      (op (globalEtale P.obj.right.left))).hom.toAddMonoidHom

/-- The coefficient comparison on global sections is evaluation of the adjunction mate on the
terminal étale object. -/
theorem etaleExtensionByZeroConverterSections_eq
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleExtensionByZeroConverterSections P F =
      (((etaleExtensionByZeroConverter P).app F).hom.app
          (op (globalEtale P.obj.right.left))).hom.toAddMonoidHom :=
  sorry

/-- The mate comparison on global sections is bijective. -/
theorem etaleExtensionByZeroConverterSections_bijective
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    Function.Bijective (etaleExtensionByZeroConverterSections P F) :=
  sorry

/-- Additive equivalence between global sections of `j_! F_ℤ` and of the
coefficient conversion of `j_! F`. -/
def etaleExtensionByZeroConverterSectionsEquiv
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} (ULift.{u} ℤ))).obj
        (etaleAbelianToIntModuleSheaf F)).obj.obj
        (op (globalEtale P.obj.right.left)) ≃+
      ((sheafCompose P.obj.right.left.smallEtaleTopology
            AddCommGrpCat.toULiftIntModule).obj
        ((abelianExtensionByZero (Compactification.Of.ι P)).obj F)).obj.obj
        (op (globalEtale P.obj.right.left)) :=
  { toFun := etaleExtensionByZeroConverterSections P F
    invFun := Function.invFun (etaleExtensionByZeroConverterSections P F)
    left_inv := Function.leftInverse_invFun (etaleExtensionByZeroConverterSections_bijective P F).injective
    right_inv := Function.rightInverse_invFun (etaleExtensionByZeroConverterSections_bijective P F).surjective
    map_add' := (etaleExtensionByZeroConverterSections P F).map_add }

/-- Coefficient conversion on the abelian global-section group of `j_! F`. -/
def etaleExtensionByZeroAbelianToConvertedSections
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    ((abelianExtensionByZero (Compactification.Of.ι P)).obj F).obj.obj
        (op (globalEtale P.obj.right.left)) →+
      ((sheafCompose P.obj.right.left.smallEtaleTopology
            AddCommGrpCat.toULiftIntModule).obj
        ((abelianExtensionByZero (Compactification.Of.ι P)).obj F)).obj.obj
        (op (globalEtale P.obj.right.left)) :=
  AddCommGrpCat.toULiftIntModuleAddHom
    (((abelianExtensionByZero (Compactification.Of.ι P)).obj F).obj.obj
      (op (globalEtale P.obj.right.left)))

/-- Conversion of abelian global sections is the additive coefficient map evaluated on the
global-section group. -/
theorem etaleExtensionByZeroAbelianToConvertedSections_eq
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleExtensionByZeroAbelianToConvertedSections P F =
      AddCommGrpCat.toULiftIntModuleAddHom
        (((abelianExtensionByZero (Compactification.Of.ι P)).obj F).obj.obj
          (op (globalEtale P.obj.right.left))) :=
  sorry

/-- Additive conversion from abelian global sections of `j_! F` to global
sections of `j_!` of the associated `ULift ℤ`-module sheaf. -/
def etaleExtensionByZeroAbelianToModuleSections
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    ((abelianExtensionByZero (Compactification.Of.ι P)).obj F).obj.obj
        (op (globalEtale P.obj.right.left)) →+
      ((etaleExtensionByZero (Compactification.Of.ι P)
            (ModuleCat.{u} (ULift.{u} ℤ))).obj
          (etaleAbelianToIntModuleSheaf F)).obj.obj
        (op (globalEtale P.obj.right.left)) :=
  (etaleExtensionByZeroConverterSectionsEquiv P F).symm.toAddMonoidHom.comp
    (etaleExtensionByZeroAbelianToConvertedSections P F)

/-- The conversion of global sections is coefficient conversion followed by
the inverse of the mate comparison. -/
theorem etaleExtensionByZeroAbelianToModuleSections_comp
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleExtensionByZeroAbelianToModuleSections P F =
      (etaleExtensionByZeroConverterSectionsEquiv P F).symm.toAddMonoidHom.comp
        (etaleExtensionByZeroAbelianToConvertedSections P F) :=
  sorry

/-- The composite additive comparison from underived `H^0_c(X, F)` to derived
`H^0_c(X, F_ℤ[0])`. -/
def globalSectionsCompactSupportDerivedHom
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F) :
    globalSectionsCompactSupportSubgroup X F →+
      etaleDerivedCohomologyCompactSupport P 0
        ((DerivedCategory.singleFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))
            (0 : ℤ)).obj (etaleAbelianToIntModuleSheaf F)) :=
  have := hF
  (etaleDerivedCohomologyCompactSupportZeroAddHom P
        (etaleAbelianToIntModuleSheaf F)).comp
    ((etaleExtensionByZeroAbelianToModuleSections P F).comp
      (globalSectionsCompactSupportCompactifyGlobalEquiv
        { P.obj.hom with left := Compactification.Of.ι P } F).toAddMonoidHom)

/-- The compactly supported comparison factors through compactification, followed by
coefficient conversion and the derived comparison from global sections of
`j_! F`. -/
theorem globalSectionsCompactSupportDerivedHom_comp
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F) :
    globalSectionsCompactSupportDerivedHom P F hF =
      (etaleDerivedCohomologyCompactSupportZeroAddHom P
            (etaleAbelianToIntModuleSheaf F)).comp
        ((etaleExtensionByZeroAbelianToModuleSections P F).comp
          (globalSectionsCompactSupportCompactifyGlobalEquiv
        { P.obj.hom with left := Compactification.Of.ι P } F).toAddMonoidHom) :=
  sorry

/-- The composite comparison `H^0_c(X, F) →+ derived H^0_c` is bijective. -/
theorem globalSectionsCompactSupportDerivedHom_bijective
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F) :
    Function.Bijective (globalSectionsCompactSupportDerivedHom P F hF) :=
  sorry

/-- For a locally torsion abelian étale sheaf on a separated finite-type scheme over a field,
compactly supported global sections are canonically additively equivalent to degree-zero
derived compactly supported cohomology. -/
def globalSectionsCompactSupportDerivedEquiv
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F) :
    globalSectionsCompactSupportSubgroup X F ≃+
      etaleDerivedCohomologyCompactSupport P 0
        ((DerivedCategory.singleFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))) (0 : ℤ)).obj
          (etaleAbelianToIntModuleSheaf F)) :=
  { toFun := globalSectionsCompactSupportDerivedHom P F hF
    invFun := Function.invFun (globalSectionsCompactSupportDerivedHom P F hF)
    left_inv := Function.leftInverse_invFun (globalSectionsCompactSupportDerivedHom_bijective P F hF).injective
    right_inv := Function.rightInverse_invFun (globalSectionsCompactSupportDerivedHom_bijective P F hF).surjective
    map_add' := (globalSectionsCompactSupportDerivedHom P F hF).map_add }

/-- The compact-support equivalence acts by the canonical composite from compactly supported
global sections to degree-zero derived cohomology. -/
theorem globalSectionsCompactSupportDerivedEquiv_apply
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F)
    (σ : globalSectionsCompactSupportSubgroup X F) :
    globalSectionsCompactSupportDerivedEquiv P F hF σ =
      globalSectionsCompactSupportDerivedHom P F hF σ :=
  sorry

/-- The identification of underived and derived `H^0_c` is the compactification
comparison, followed by coefficient conversion of `j_! F`
and the derived identification of `Γ(X̄, j_! F)` with derived `H^0_c`. -/
theorem globalSectionsCompactSupportDerivedEquiv_comp
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F) :
    (globalSectionsCompactSupportDerivedEquiv P F hF).toAddMonoidHom =
      (etaleDerivedCohomologyCompactSupportZeroAddHom P
            (etaleAbelianToIntModuleSheaf F)).comp
        ((etaleExtensionByZeroAbelianToModuleSections P F).comp
          (globalSectionsCompactSupportCompactifyGlobalEquiv
        { P.obj.hom with left := Compactification.Of.ι P } F).toAddMonoidHom) :=
  sorry

/-- A torsion abelian sheaf remains torsion after conversion to a sheaf of
`ℤ`-modules and placement in degree zero in the derived category. -/
theorem etaleAbelianToIntModuleSheaf_single_isTorsion
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F) :
    etaleDerivedIsTorsion
      ((DerivedCategory.singleFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))) (0 : ℤ)).obj
        (etaleAbelianToIntModuleSheaf F)) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
