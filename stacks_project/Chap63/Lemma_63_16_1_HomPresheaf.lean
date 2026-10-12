/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import stacks_project.Chap63.Lemma_63_16_1_UpperShriek

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Linear
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable (Λ : Type u) [CommRing Λ]
variable [∀ U : Scheme.{u}, HasWeakSheafify U.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ (U V : Scheme.{u}) (f : U ⟶ V) [Etale f]
    (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (etaleRestriction f).op.HasLeftKanExtension F]

/-- The constant étale sheaf of `Λ`-modules on a scheme. -/
def etaleConstantModule (S : Scheme.{u}) :
    Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ) :=
  (constantSheaf S.smallEtaleTopology (ModuleCat.{u} Λ)).obj (ModuleCat.of Λ Λ)

/-- The constant sheaf of `Λ`-modules is the sheafification of the constant
presheaf on `ModuleCat.of Λ Λ`. -/
theorem etaleConstantModule_def (S : Scheme.{u}) :
    etaleConstantModule Λ S =
      (constantSheaf S.smallEtaleTopology (ModuleCat.{u} Λ)).obj
        (ModuleCat.of Λ Λ) :=
  sorry

/-- Extension by zero of the constant `Λ`-module sheaf along an étale morphism. -/
def etaleExtensionByZeroConstant {U S : Scheme.{u}} (j : U ⟶ S) [Etale j] :
    Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ) :=
  (etaleExtensionByZero j (ModuleCat.{u} Λ)).obj (etaleConstantModule Λ U)

/-- Evaluating `j_! Λ` applies étale extension by zero to the constant sheaf. -/
theorem etaleExtensionByZeroConstant_obj {U S : Scheme.{u}} (j : U ⟶ S)
    [Etale j] :
    etaleExtensionByZeroConstant Λ j =
      (etaleExtensionByZero j (ModuleCat.{u} Λ)).obj (etaleConstantModule Λ U) :=
  sorry

/-- Bundled extension by zero of the constant sheaf along an object of the
small étale site. -/
def etaleExtensionByZeroConstantOver {S : Scheme.{u}} (U : S.Etale)
    (hU : Etale U.hom := U.prop) :
    Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ) :=
  @etaleExtensionByZeroConstant Λ _ _ _ U.left S U.hom hU

/-- Bundled `j_! Λ` is extension by zero of the constant sheaf along `U.hom`. -/
theorem etaleExtensionByZeroConstantOver_obj {S : Scheme.{u}} (U : S.Etale)
    (hU : Etale U.hom := U.prop) :
    etaleExtensionByZeroConstantOver Λ U =
      @etaleExtensionByZeroConstant Λ _ _ _ U.left S U.hom hU :=
  sorry

/-- Restriction along a composite étale morphism is the composite of the
restriction functors. -/
def etaleRestrictionCompIso {U U' S : Scheme.{u}} (h : U ⟶ U') (g : U' ⟶ S)
    (f : U ⟶ S) [Etale h] [Etale g] [Etale f] (hf : f = h ≫ g) :
    etaleRestriction f ≅ etaleRestriction h ⋙ etaleRestriction g :=
  MorphismProperty.Over.mapComp (Q := (⊤ : MorphismProperty Scheme))
    (inferInstance : Etale h) (inferInstance : Etale g) f hf

/-- Sheaf restriction along a composite étale morphism is the composite of
sheaf restrictions. -/
def etaleRestrictionSheafCompIso {U U' S : Scheme.{u}} (h : U ⟶ U') (g : U' ⟶ S)
    (f : U ⟶ S) [Etale h] [Etale g] [Etale f] (hf : f = h ≫ g) :
    etaleRestrictionSheaf g (ModuleCat.{u} Λ) ⋙
        etaleRestrictionSheaf h (ModuleCat.{u} Λ) ≅
      etaleRestrictionSheaf f (ModuleCat.{u} Λ) :=
  Functor.sheafPushforwardContinuousComp'
    (etaleRestrictionCompIso h g f hf).symm (ModuleCat.{u} Λ)
    U.smallEtaleTopology U'.smallEtaleTopology S.smallEtaleTopology

/-- Extension by zero along a composite étale morphism is the composite of the
extension-by-zero functors. -/
def etaleExtensionByZeroCompIso {U U' S : Scheme.{u}} (h : U ⟶ U') (g : U' ⟶ S)
    (f : U ⟶ S) [Etale h] [Etale g] [Etale f] (hf : f = h ≫ g) :
    etaleExtensionByZero f (ModuleCat.{u} Λ) ≅
      etaleExtensionByZero h (ModuleCat.{u} Λ) ⋙
        etaleExtensionByZero g (ModuleCat.{u} Λ) :=
  Adjunction.leftAdjointUniq
    (Adjunction.ofNatIsoRight
      (etaleExtensionByZero_adjunction f (ModuleCat.{u} Λ))
      (etaleRestrictionSheafCompIso Λ h g f hf).symm)
    ((etaleExtensionByZero_adjunction h (ModuleCat.{u} Λ)).comp
      (etaleExtensionByZero_adjunction g (ModuleCat.{u} Λ)))

/-- The canonical map from the constant sheaf on the source to the restriction
of the constant sheaf on the target. -/
def etaleConstantToRestriction {U S : Scheme.{u}} (j : U ⟶ S) [Etale j] :
    etaleConstantModule Λ U ⟶
      (etaleRestrictionSheaf j (ModuleCat.{u} Λ)).obj (etaleConstantModule Λ S) :=
  ((sheafificationAdjunction U.smallEtaleTopology (ModuleCat.{u} Λ)).homEquiv
      ((Functor.const U.Etaleᵒᵖ).obj (ModuleCat.of Λ Λ))
      ((etaleRestrictionSheaf j (ModuleCat.{u} Λ)).obj
        (etaleConstantModule Λ S))).symm
    ((Functor.constCompWhiskeringLeftIso
        (J := U.Etaleᵒᵖ) (D := S.Etaleᵒᵖ) (C := ModuleCat.{u} Λ)
        (etaleRestriction j).op).inv.app (ModuleCat.of Λ Λ) ≫
      whiskerLeft (etaleRestriction j).op
        (toSheafify S.smallEtaleTopology
          ((Functor.const S.Etaleᵒᵖ).obj (ModuleCat.of Λ Λ))))

/-- The étale trace `Tr_j : j_! Λ ⟶ Λ` obtained from the extension-by-zero
counit after identifying the restriction of the constant sheaf. -/
def etaleTrace {U S : Scheme.{u}} (j : U ⟶ S) [Etale j] :
    etaleExtensionByZeroConstant Λ j ⟶ etaleConstantModule Λ S :=
  ((etaleExtensionByZero_adjunction j (ModuleCat.{u} Λ)).homEquiv
      (etaleConstantModule Λ U) (etaleConstantModule Λ S)).symm
    (etaleConstantToRestriction Λ j)

/-- The étale trace is the adjunct of the canonical comparison of constant
sheaves. -/
theorem etaleTrace_spec {U S : Scheme.{u}} (j : U ⟶ S) [Etale j] :
    etaleTrace Λ j =
      ((etaleExtensionByZero_adjunction j (ModuleCat.{u} Λ)).homEquiv
          (etaleConstantModule Λ U) (etaleConstantModule Λ S)).symm
        (etaleConstantToRestriction Λ j) :=
  sorry

/-- Functoriality of `j_! Λ` along an étale morphism of étale `S`-schemes,
using the étale trace on the source of the refinement. -/
def etaleTraceOver {S : Scheme.{u}} {U U' : S.Etale} (φ : U ⟶ U')
    (hU : Etale U.hom := U.prop) (hU' : Etale U'.hom := U'.prop) :
    etaleExtensionByZeroConstantOver Λ U ⟶
      etaleExtensionByZeroConstantOver Λ U' :=
  (@etaleExtensionByZeroCompIso Λ _ _ _ U.left U'.left S φ.left U'.hom U.hom
      inferInstance hU' hU (MorphismProperty.Over.w φ).symm).hom.app
    (etaleConstantModule Λ U.left) ≫
  (@etaleExtensionByZero U'.left S U'.hom hU' (ModuleCat.{u} Λ)).map
    (etaleTrace Λ φ.left)

/-- Trace functoriality of bundled `j_! Λ` is a morphism of étale sheaves of
`Λ`-modules. -/
theorem etaleTraceOver_comp {S : Scheme.{u}} {U U' U'' : S.Etale}
    (φ : U ⟶ U') (ψ : U' ⟶ U'') :
    etaleTraceOver Λ φ ≫ etaleTraceOver Λ ψ = etaleTraceOver Λ (φ ≫ ψ) :=
  sorry

/-- The identity étale `U`-scheme, used to evaluate sheaves of modules. -/
def etaleIdentity {S : Scheme.{u}} (U : S.Etale) : U.left.Etale :=
  Etale.mk (𝟙 U.left)

/-- The identity étale object is `Etale.mk` of the identity morphism. -/
theorem etaleIdentity_eq {S : Scheme.{u}} (U : S.Etale) :
    etaleIdentity U = Etale.mk (𝟙 U.left) :=
  sorry

/-- Postcomposition with `U ⟶ S` sends the identity étale `U`-scheme to `U`. -/
def etaleRestriction_identity {S : Scheme.{u}} (U : S.Etale)
    (hU : Etale U.hom := U.prop) :
    (@etaleRestriction U.left S U.hom hU).obj (etaleIdentity U) ≅ U :=
  MorphismProperty.Over.isoMk (Iso.refl _) sorry

/-- The underlying scheme morphism of `etaleRestriction_identity` is the
identity. -/
theorem etaleRestriction_identity_hom_left {S : Scheme.{u}} (U : S.Etale)
    (hU : Etale U.hom := U.prop) :
    (etaleRestriction_identity U).hom.left = 𝟙 U.left :=
  sorry

/-- Sheafification of the constant presheaf, evaluated at the identity étale
object. -/
def etaleConstantSheafifyUnit {S : Scheme.{u}} (U : S.Etale) :
    ModuleCat.of Λ Λ ⟶
      (etaleConstantModule Λ U.left).obj.obj (op (etaleIdentity U)) :=
  (toSheafify U.left.smallEtaleTopology
      ((Functor.const U.left.Etaleᵒᵖ).obj (ModuleCat.of Λ Λ))).app
    (op (etaleIdentity U))

/-- Sheafification of the constant presheaf at the identity is `toSheafify`. -/
theorem etaleConstantSheafifyUnit_spec {S : Scheme.{u}} (U : S.Etale) :
    etaleConstantSheafifyUnit Λ U =
      (toSheafify U.left.smallEtaleTopology
          ((Functor.const U.left.Etaleᵒᵖ).obj (ModuleCat.of Λ Λ))).app
        (op (etaleIdentity U)) :=
  sorry

/-- The unit section of the constant sheaf of `Λ`-modules at the identity étale
object, obtained from `toSheafify` of `(1 : Λ)`. -/
def etaleConstantUnitSection {S : Scheme.{u}} (U : S.Etale) :
    (etaleConstantModule Λ U.left).obj.obj (op (etaleIdentity U)) :=
  ConcreteCategory.hom (C := ModuleCat.{u} Λ)
    (etaleConstantSheafifyUnit Λ U) (1 : Λ)

/-- The unit section is sheafification of the unit of `Λ`. -/
theorem etaleConstantUnitSection_spec {S : Scheme.{u}} (U : S.Etale) :
    etaleConstantUnitSection Λ U =
      ConcreteCategory.hom (C := ModuleCat.{u} Λ)
        (etaleConstantSheafifyUnit Λ U) (1 : Λ) :=
  sorry


variable {Y : Scheme.{u}} (X : Over Y)
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (P : Compactification.Of Y X)
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [((etaleDerivedLowerShriek X P :
    EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ)).IsLeftAdjoint]
variable [Linear Λ (EtaleDerived Y Λ)]
variable [Linear Λ (EtaleDerived X.left Λ)]
variable [HasSheafify (AffineEtale.topology X.left) (ModuleCat.{u} Λ)]
variable [((etaleDerivedLowerShriek X P :
    EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ)).CommShift ℤ]

/-- The covariant functor `U ↦ R(U ⟶ Y)_! Λ` on `X.left.AffineEtale`, realized
as `Rf_!(j_U ! Λ)` via shriek composition. -/
def etaleDerivedLowerShriekConstant :
    X.left.AffineEtale ⥤ EtaleDerived Y Λ where
  obj U :=
    (etaleDerivedLowerShriek X P).obj
      ((DerivedCategory.singleFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
        (etaleExtensionByZeroConstantOver Λ ((AffineEtale.Spec X.left).obj U)))
  map {U U'} f :=
    (etaleDerivedLowerShriek X P).map
      ((DerivedCategory.singleFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).map
        (etaleTraceOver Λ ((AffineEtale.Spec X.left).map f)))
  map_id := sorry
  map_comp := sorry

/-- Evaluating the affine constant lower shriek on `U` yields
`Rf_!(j_U ! Λ)`. -/
theorem etaleDerivedLowerShriekConstant_obj (U : X.left.AffineEtale) :
    (etaleDerivedLowerShriekConstant Λ X P).obj U =
      (etaleDerivedLowerShriek X P).obj
        ((DerivedCategory.singleFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
          (etaleExtensionByZeroConstantOver Λ
            ((AffineEtale.Spec X.left).obj U))) :=
  sorry

/-- The Hom presheaf `U ↦ Hom_Y(R(U ⟶ Y)_! Λ, K⟦n⟧)` on the affine étale site. -/
def etaleDerivedUpperShriekHomPresheaf (K : EtaleDerived Y Λ) (n : ℤ) :
    X.left.AffineEtaleᵒᵖ ⥤ ModuleCat.{u} Λ :=
  (etaleDerivedLowerShriekConstant Λ X P).op ⋙
    (linearYoneda Λ (EtaleDerived Y Λ)).obj (K⟦n⟧)

/-- The value of the Hom presheaf at `U` is the `Λ`-module of maps
`R(U ⟶ Y)_! Λ ⟶ K⟦n⟧` in `D(Y_étale, Λ)`. -/
theorem etaleDerivedUpperShriekHomPresheaf_obj (K : EtaleDerived Y Λ) (n : ℤ)
    (U : X.left.AffineEtaleᵒᵖ) :
    (etaleDerivedUpperShriekHomPresheaf Λ X P K n).obj U =
      ((linearYoneda Λ (EtaleDerived Y Λ)).obj (K⟦n⟧)).obj
        (op ((etaleDerivedLowerShriekConstant Λ X P).obj U.unop)) :=
  sorry

/-- Restriction of an étale sheaf of `Λ`-modules to the affine étale site. -/
def etaleCohomologyRestrictAffine (S : Scheme.{u})
    [HasSheafify (AffineEtale.topology S) (ModuleCat.{u} Λ)]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) :
    Sheaf (AffineEtale.topology S) (ModuleCat.{u} Λ) :=
  (AffineEtale.sheafEquiv S (ModuleCat.{u} Λ)).inverse.obj F

/-- Restriction to the affine étale site is the inverse of
`AffineEtale.sheafEquiv`. -/
theorem etaleCohomologyRestrictAffine_def (S : Scheme.{u})
    [HasSheafify (AffineEtale.topology S) (ModuleCat.{u} Λ)]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) :
    etaleCohomologyRestrictAffine Λ S F =
      (AffineEtale.sheafEquiv S (ModuleCat.{u} Λ)).inverse.obj F :=
  sorry

/-- The `Λ`-linear map on Hom-modules induced by the adjunction `Rf_! ⊣ Rf^!`. -/
def etaleDerivedLowerShriekAdjunctionHomModule
    (L : EtaleDerived X.left Λ) (K : EtaleDerived Y Λ) :
    ((linearYoneda Λ (EtaleDerived Y Λ)).obj K).obj
        (op ((etaleDerivedLowerShriek X P).obj L)) ⟶
      ((linearYoneda Λ (EtaleDerived X.left Λ)).obj
          ((etaleDerivedUpperShriek X Λ P).obj K)).obj (op L) :=
  ModuleCat.ofHom
    { toFun := (etaleDerivedLowerShriekAdjunction X Λ P).homEquiv L K
      map_add' := sorry
      map_smul' := sorry }

/-- The Hom-module map of `Rf_! ⊣ Rf^!` is the adjunction hom-equivalence. -/
theorem etaleDerivedLowerShriekAdjunctionHomModule_spec
    (L : EtaleDerived X.left Λ) (K : EtaleDerived Y Λ)
    (φ : (etaleDerivedLowerShriek X P).obj L ⟶ K) :
    (etaleDerivedLowerShriekAdjunctionHomModule Λ X P L K) φ =
      (etaleDerivedLowerShriekAdjunction X Λ P).homEquiv L K φ :=
  sorry

/-- Applying degree-zero homology to maps out of `j_! Λ` placed in degree `0`. -/
def etaleDerivedHomologyMapModule (M : EtaleDerived X.left Λ) (n : ℤ)
    (U : X.left.Etale)
    (φ :
      (DerivedCategory.singleFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
        (etaleExtensionByZeroConstantOver Λ U) ⟶
      M⟦n⟧) :
    (DerivedCategory.homologyFunctor
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
      ((DerivedCategory.singleFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
        (etaleExtensionByZeroConstantOver Λ U)) ⟶
    (DerivedCategory.homologyFunctor
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
      (M⟦n⟧) :=
  (DerivedCategory.homologyFunctor
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).map φ

/-- Degree-zero homology of maps out of `j_! Λ` is `homologyFunctor 0`. -/
theorem etaleDerivedHomologyMapModule_spec (M : EtaleDerived X.left Λ)
    (n : ℤ) (U : X.left.Etale)
    (φ :
      (DerivedCategory.singleFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
        (etaleExtensionByZeroConstantOver Λ U) ⟶
      M⟦n⟧) :
    etaleDerivedHomologyMapModule Λ X M n U φ =
      (DerivedCategory.homologyFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).map φ :=
  sorry

/-- Precomposition with the inverse of
`singleFunctorCompHomologyFunctorIso` on `j_! Λ`. -/
def etaleDerivedSingleHomologyIsoInvModule (M : EtaleDerived X.left Λ)
    (n : ℤ) (U : X.left.Etale)
    (φ :
      (DerivedCategory.homologyFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
        ((DerivedCategory.singleFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
          (etaleExtensionByZeroConstantOver Λ U)) ⟶
      (DerivedCategory.homologyFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
        (M⟦n⟧)) :
    etaleExtensionByZeroConstantOver Λ U ⟶
      (DerivedCategory.homologyFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
        (M⟦n⟧) :=
  ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).inv.app
      (etaleExtensionByZeroConstantOver Λ U)) ≫ φ

/-- The inverse homology comparison is left composition with
`singleFunctorCompHomologyFunctorIso.inv`. -/
theorem etaleDerivedSingleHomologyIsoInvModule_spec
    (M : EtaleDerived X.left Λ) (n : ℤ) (U : X.left.Etale)
    (φ :
      (DerivedCategory.homologyFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
        ((DerivedCategory.singleFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
          (etaleExtensionByZeroConstantOver Λ U)) ⟶
      (DerivedCategory.homologyFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
        (M⟦n⟧)) :
    etaleDerivedSingleHomologyIsoInvModule Λ X M n U φ =
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).inv.app
          (etaleExtensionByZeroConstantOver Λ U)) ≫ φ :=
  sorry

/-- Postcomposition with the degree-zero homology shift isomorphism
`H^0(-⟦n⟧) ⟶ H^n`. -/
def etaleDerivedHomologyIsoShiftModule (M : EtaleDerived X.left Λ) (n : ℤ)
    (U : X.left.Etale)
    (φ :
      etaleExtensionByZeroConstantOver Λ U ⟶
        (DerivedCategory.homologyFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
          (M⟦n⟧)) :
    etaleExtensionByZeroConstantOver Λ U ⟶
      (DerivedCategory.homologyFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj M :=
  φ ≫
    (((DerivedCategory.homologyFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
          0).isoShift n).hom.app M)

/-- The homology shift comparison is right composition with `isoShift n`. -/
theorem etaleDerivedHomologyIsoShiftModule_spec
    (M : EtaleDerived X.left Λ) (n : ℤ) (U : X.left.Etale)
    (φ :
      etaleExtensionByZeroConstantOver Λ U ⟶
        (DerivedCategory.homologyFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
          (M⟦n⟧)) :
    etaleDerivedHomologyIsoShiftModule Λ X M n U φ =
      φ ≫
        (((DerivedCategory.homologyFunctor
              (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
              0).isoShift n).hom.app M) :=
  sorry

/-- The `Λ`-linear map on Hom-modules induced by `j_! ⊣ j^*`. -/
def etaleExtensionByZeroAdjunctionHomModule
    {U S : Scheme.{u}} (j : U ⟶ S) (h : Etale j := by infer_instance)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ))
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) :
    ((linearYoneda Λ
          (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))).obj G).obj
        (op ((@etaleExtensionByZero U S j h (ModuleCat.{u} Λ)).obj F)) ⟶
      ((linearYoneda Λ
          (Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ))).obj
        ((@etaleRestrictionSheaf U S j h (ModuleCat.{u} Λ)).obj G)).obj
        (op F) :=
  ModuleCat.ofHom
    { toFun := (@etaleExtensionByZero_adjunction U S j h
          (ModuleCat.{u} Λ)).homEquiv F G
      map_add' := sorry
      map_smul' := sorry }

/-- The Hom-module map of `j_! ⊣ j^*` is the adjunction hom-equivalence. -/
theorem etaleExtensionByZeroAdjunctionHomModule_spec
    {U S : Scheme.{u}} (j : U ⟶ S) (h : Etale j := by infer_instance)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ))
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
    (φ : (@etaleExtensionByZero U S j h (ModuleCat.{u} Λ)).obj F ⟶ G) :
    etaleExtensionByZeroAdjunctionHomModule Λ j h F G φ =
      (@etaleExtensionByZero_adjunction U S j h
          (ModuleCat.{u} Λ)).homEquiv F G φ :=
  sorry

/-- Evaluation of a sheaf morphism `Λ_U ⟶ G|_U` at the identity étale object,
using `Sheaf.homEquiv` and the unit section of `Λ`. -/
def etaleSheafEvalUnitSection {S : Scheme.{u}} (U : S.Etale)
    (hU : Etale U.hom := U.prop)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
    (φ :
      etaleConstantModule Λ U.left ⟶
        (@etaleRestrictionSheaf U.left S U.hom hU (ModuleCat.{u} Λ)).obj G) :
    ((@etaleRestrictionSheaf U.left S U.hom hU (ModuleCat.{u} Λ)).obj G).obj.obj
      (op (etaleIdentity U)) :=
  ConcreteCategory.hom (C := ModuleCat.{u} Λ)
    ((Sheaf.homEquiv φ).app (op (etaleIdentity U)))
    (etaleConstantUnitSection Λ U)

/-- Evaluation at the identity applies `Sheaf.homEquiv` to the unit section of
`Λ`. -/
theorem etaleSheafEvalUnitSection_spec {S : Scheme.{u}} (U : S.Etale)
    (hU : Etale U.hom := U.prop)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
    (φ :
      etaleConstantModule Λ U.left ⟶
        (@etaleRestrictionSheaf U.left S U.hom hU (ModuleCat.{u} Λ)).obj G) :
    etaleSheafEvalUnitSection Λ U hU G φ =
      ConcreteCategory.hom (C := ModuleCat.{u} Λ)
        ((Sheaf.homEquiv φ).app (op (etaleIdentity U)))
        (etaleConstantUnitSection Λ U) :=
  sorry

/-- Restriction of sections of an étale sheaf along the inverse of
`etaleRestriction_identity`, sending sections on the restricted identity to
sections on `U`. -/
def etaleCohomologyRestrictIdentityInv {S : Scheme.{u}} (U : S.Etale)
    (hU : Etale U.hom := U.prop)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) :
    G.obj.obj (op ((@etaleRestriction U.left S U.hom hU).obj
        (etaleIdentity U))) ⟶
      G.obj.obj (op U) :=
  G.obj.map (etaleRestriction_identity U hU).inv.op

/-- Restriction along the identity comparison uses
`(etaleRestriction_identity U).inv.op`. -/
theorem etaleCohomologyRestrictIdentityInv_spec {S : Scheme.{u}}
    (U : S.Etale) (hU : Etale U.hom := U.prop)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) :
    etaleCohomologyRestrictIdentityInv Λ U hU G =
      G.obj.map (etaleRestriction_identity U hU).inv.op :=
  sorry

/-- Evaluation of `Hom_U(Λ_U, G|_U)` at the unit section of `Λ`, then restriction
along `(etaleRestriction_identity U).inv` to a section of `G` on `U`. -/
def etaleSheafEvalUnitModule {S : Scheme.{u}} (U : S.Etale)
    (hU : Etale U.hom := U.prop)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
    (φ :
      etaleConstantModule Λ U.left ⟶
        (@etaleRestrictionSheaf U.left S U.hom hU (ModuleCat.{u} Λ)).obj G) :
    G.obj.obj (op U) :=
  etaleCohomologyRestrictIdentityInv Λ U hU G
    (etaleSheafEvalUnitSection Λ U hU G φ)

/-- The unit-section evaluation is `etaleSheafEvalUnitSection` followed by
`etaleCohomologyRestrictIdentityInv`. -/
theorem etaleSheafEvalUnitModule_spec {S : Scheme.{u}} (U : S.Etale)
    (hU : Etale U.hom := U.prop)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
    (φ :
      etaleConstantModule Λ U.left ⟶
        (@etaleRestrictionSheaf U.left S U.hom hU (ModuleCat.{u} Λ)).obj G) :
    etaleSheafEvalUnitModule Λ U hU G φ =
      etaleCohomologyRestrictIdentityInv Λ U hU G
        (etaleSheafEvalUnitSection Λ U hU G φ) :=
  sorry

/-- The identification `Hom_X(j_! Λ, M⟦n⟧) ⟶ H^n(U, M)` obtained by composing
degree-zero homology, the inverse of `singleFunctorCompHomologyFunctorIso`,
the homology shift isomorphism, the extension-by-zero adjunction, and
evaluation of the unit section of `Λ` followed by restriction along
`(etaleRestriction_identity U).inv`. -/
def etaleDerivedHomShriekConstantToCohomology (M : EtaleDerived X.left Λ)
    (n : ℤ) (U : X.left.Etale)
    (hU : Etale U.hom := U.prop) :
    ((linearYoneda Λ (EtaleDerived X.left Λ)).obj (M⟦n⟧)).obj
        (op ((DerivedCategory.singleFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
          (etaleExtensionByZeroConstantOver Λ U))) ⟶
      ((DerivedCategory.homologyFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj M).obj.obj
        (op U) :=
  ModuleCat.ofHom
    { toFun := fun φ ↦
        etaleSheafEvalUnitModule Λ U hU
          ((DerivedCategory.homologyFunctor
              (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj M)
          (etaleExtensionByZeroAdjunctionHomModule Λ U.hom hU
            (etaleConstantModule Λ U.left)
            ((DerivedCategory.homologyFunctor
                (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj M)
            (etaleDerivedHomologyIsoShiftModule Λ X M n U
              (etaleDerivedSingleHomologyIsoInvModule Λ X M n U
                (etaleDerivedHomologyMapModule Λ X M n U φ))))
      map_add' := sorry
      map_smul' := sorry }

/-- The cohomology comparison applies the named homology, shift, adjunction, and
unit-section evaluation maps in that order. -/
theorem etaleDerivedHomShriekConstantToCohomology_spec
    (M : EtaleDerived X.left Λ) (n : ℤ) (U : X.left.Etale)
    (hU : Etale U.hom := U.prop)
    (φ :
      (DerivedCategory.singleFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
        (etaleExtensionByZeroConstantOver Λ U) ⟶
      M⟦n⟧) :
    etaleDerivedHomShriekConstantToCohomology Λ X M n U hU φ =
      etaleSheafEvalUnitModule Λ U hU
        ((DerivedCategory.homologyFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj M)
        (etaleExtensionByZeroAdjunctionHomModule Λ U.hom hU
          (etaleConstantModule Λ U.left)
          ((DerivedCategory.homologyFunctor
              (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj M)
          (etaleDerivedHomologyIsoShiftModule Λ X M n U
            (etaleDerivedSingleHomologyIsoInvModule Λ X M n U
              (etaleDerivedHomologyMapModule Λ X M n U φ)))) :=
  sorry

/-- Component of the comparison at an affine étale object, sending a derived
Hom to the corresponding section of `H^n(Rf^! K)`. -/
def etaleDerivedUpperShriekHomToCohomology (K : EtaleDerived Y Λ) (n : ℤ)
    (U : X.left.AffineEtaleᵒᵖ) :
    (etaleDerivedUpperShriekHomPresheaf Λ X P K n).obj U ⟶
      ((etaleCohomologyRestrictAffine Λ X.left
          ((DerivedCategory.homologyFunctor
              (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj
            ((etaleDerivedUpperShriek X Λ P).obj K))).obj.obj U) :=
  let jU := (AffineEtale.Spec X.left).obj U.unop
  let L :=
    (DerivedCategory.singleFunctor
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
      (etaleExtensionByZeroConstantOver Λ jU)
  etaleDerivedLowerShriekAdjunctionHomModule Λ X P L (K⟦n⟧) ≫
    ModuleCat.ofHom
      (rightComp Λ L
        (((etaleDerivedUpperShriek X Λ P).commShiftIso n).hom.app K)) ≫
      etaleDerivedHomShriekConstantToCohomology Λ X
        ((etaleDerivedUpperShriek X Λ P).obj K) n jU

/-- The affine comparison component is adjunction, then the shift isomorphism
of `Rf^!`, then the `Hom(j_! Λ, -) → H^n` identification. -/
theorem etaleDerivedUpperShriekHomToCohomology_spec (K : EtaleDerived Y Λ)
    (n : ℤ) (U : X.left.AffineEtaleᵒᵖ) :
    etaleDerivedUpperShriekHomToCohomology Λ X P K n U =
      (let jU := (AffineEtale.Spec X.left).obj U.unop
        let L :=
          (DerivedCategory.singleFunctor
              (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
            (etaleExtensionByZeroConstantOver Λ jU)
        etaleDerivedLowerShriekAdjunctionHomModule Λ X P L (K⟦n⟧) ≫
          ModuleCat.ofHom
            (rightComp Λ L
              (((etaleDerivedUpperShriek X Λ P).commShiftIso n).hom.app K)) ≫
            etaleDerivedHomShriekConstantToCohomology Λ X
              ((etaleDerivedUpperShriek X Λ P).obj K) n jU) :=
  sorry

/-- The presheaf map from `U ↦ Hom_Y(R(U ⟶ Y)_! Λ, K⟦n⟧)` to the restriction
of `H^n(Rf^! K)` to `X_affine,étale`. -/
def etaleDerivedUpperShriekHomPresheafToRestriction (K : EtaleDerived Y Λ)
    (n : ℤ) :
    etaleDerivedUpperShriekHomPresheaf Λ X P K n ⟶
      (sheafToPresheaf (AffineEtale.topology X.left) (ModuleCat.{u} Λ)).obj
        (etaleCohomologyRestrictAffine Λ X.left
          ((DerivedCategory.homologyFunctor
              (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj
            ((etaleDerivedUpperShriek X Λ P).obj K))) where
  app U := etaleDerivedUpperShriekHomToCohomology Λ X P K n U
  naturality := sorry

/-- The comparison morphism from the sheaf associated to
`U ↦ Hom_Y(R(U ⟶ Y)_! Λ, K⟦n⟧)` to the restriction of `H^n(Rf^! K)` to the
affine étale site. -/
def etaleDerivedUpperShriekCohomologyAffineComparison (K : EtaleDerived Y Λ)
    (n : ℤ) :
    (presheafToSheaf (AffineEtale.topology X.left) (ModuleCat.{u} Λ)).obj
        (etaleDerivedUpperShriekHomPresheaf Λ X P K n) ⟶
      etaleCohomologyRestrictAffine Λ X.left
        ((DerivedCategory.homologyFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj
          ((etaleDerivedUpperShriek X Λ P).obj K)) :=
  ((sheafificationAdjunction (AffineEtale.topology X.left)
        (ModuleCat.{u} Λ)).homEquiv
      (etaleDerivedUpperShriekHomPresheaf Λ X P K n)
      (etaleCohomologyRestrictAffine Λ X.left
        ((DerivedCategory.homologyFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj
          ((etaleDerivedUpperShriek X Λ P).obj K)))).symm
    (etaleDerivedUpperShriekHomPresheafToRestriction Λ X P K n)

/-- The comparison is the sheafification of the Hom-presheaf map into the
affine restriction of `H^n(Rf^! K)`. -/
theorem etaleDerivedUpperShriekCohomologyAffineComparison_spec
    (K : EtaleDerived Y Λ) (n : ℤ) :
    etaleDerivedUpperShriekCohomologyAffineComparison Λ X P K n =
      ((sheafificationAdjunction (AffineEtale.topology X.left)
            (ModuleCat.{u} Λ)).homEquiv
          (etaleDerivedUpperShriekHomPresheaf Λ X P K n)
          (etaleCohomologyRestrictAffine Λ X.left
            ((DerivedCategory.homologyFunctor
                (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj
              ((etaleDerivedUpperShriek X Λ P).obj K)))).symm
        (etaleDerivedUpperShriekHomPresheafToRestriction Λ X P K n) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
