module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain.ExactFirst
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.DerivedSections
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Frobenius

/-! # Geometric Frobenius on derived étale module sections -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open Opposite ComplexShape
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

open AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k]

/-- The geometric fibre `X_k̄` of a scheme over a field. -/
abbrev geometricFibre (X : SchemeOverField k) : Scheme.{u} :=
  FieldExtension.baseChange k (AlgebraicClosure k) X.hom

/-- Unfolding of the geometric fibre as field-extension base change to the
algebraic closure. -/
theorem geometricFibre_eq (X : SchemeOverField k) :
    geometricFibre X = FieldExtension.baseChange k (AlgebraicClosure k) X.hom :=
  rfl

variable [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {Λ : Type u} [Ring Λ]
variable (X : SchemeOverField k)
variable [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify (geometricFibre X).smallEtaleTopology (ModuleCat.{u} Λ)]
variable [Abelian (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [Abelian (Sheaf (geometricFibre X).smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf (geometricFibre X).smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback (geometricFrobenius_ofFiniteField X)).op.HasLeftKanExtension P]
variable [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback
        (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).op.HasLeftKanExtension P]
variable [∀ P : (geometricFibre X).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback (geometricFrobeniusBaseChange X)).op.HasLeftKanExtension P]
variable [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback
        (geometricFrobeniusBaseChange X ≫
          FieldExtension.toSource k (AlgebraicClosure k) X.hom)).op.HasLeftKanExtension P]
variable [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback
        (FieldExtension.toSource k (AlgebraicClosure k) X.hom ≫
          geometricFrobenius_ofFiniteField X)).op.HasLeftKanExtension P]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

/-- Canonical identification `π_X⁻¹ F ≅ F` of sheaves of left `Λ`-modules, induced
by the small-étale site isomorphism of geometric Frobenius. -/
def geometricFrobeniusModuleIso :
    Sheaf.smallEtaleInverseImage (geometricFrobenius_ofFiniteField X) (ModuleCat.{u} Λ) ≅
      𝟭 (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  Adjunction.leftAdjointUniq
    ((smallEtalePullback (geometricFrobenius_ofFiniteField X)).sheafAdjunctionContinuous
      (ModuleCat.{u} Λ) X.left.smallEtaleTopology X.left.smallEtaleTopology)
    (Adjunction.id.ofNatIsoRight
      (sheafPushforwardContinuousId'
        (geometricFrobenius_smallEtalePullbackIso X).symm (ModuleCat.{u} Λ)
        X.left.smallEtaleTopology).symm)

/-- The sheaf-level geometric Frobenius identification is left-adjoint uniqueness
for the site isomorphism `𝟭 ≅ smallEtalePullback π_X`. -/
theorem geometricFrobeniusModuleIso_spec :
    geometricFrobeniusModuleIso X =
      Adjunction.leftAdjointUniq
        ((smallEtalePullback (geometricFrobenius_ofFiniteField X)).sheafAdjunctionContinuous
          (ModuleCat.{u} Λ) X.left.smallEtaleTopology X.left.smallEtaleTopology)
        (Adjunction.id.ofNatIsoRight
          (sheafPushforwardContinuousId'
            (geometricFrobenius_smallEtalePullbackIso X).symm (ModuleCat.{u} Λ)
            X.left.smallEtaleTopology).symm) :=
  rfl

/-- Bundled exact-functor isomorphism underlying `geometricFrobeniusModuleIso`. -/
def geometricFrobeniusExactIso :
    ExactFunctor.of (Sheaf.smallEtaleInverseImage (geometricFrobenius_ofFiniteField X) (ModuleCat.{u} Λ)) ≅
      ExactFunctor.id (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  ObjectProperty.isoMk _ (geometricFrobeniusModuleIso X)

/-- Derived identification `π_X⁻¹ K ≅ K` induced by the sheaf-level geometric
Frobenius iso. -/
def geometricFrobeniusDerivedIso :
    (Sheaf.smallEtaleInverseImage (geometricFrobenius_ofFiniteField X) (ModuleCat.{u} Λ)).mapDerivedCategory ≅
      𝟭 (DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :=
  ExactFunctor.MapDerivedCategory.mapIso (geometricFrobeniusExactIso X) ≪≫
    ExactFunctor.MapDerivedCategory.idFunctorIso _

/-- Canonical comparison `c_K : π_X⁻¹ K ⟶ K` on derived étale sheaves of left
`Λ`-modules. -/
def geometricFrobeniusComparison
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (Sheaf.smallEtaleInverseImage (geometricFrobenius_ofFiniteField X) (ModuleCat.{u} Λ)).mapDerivedCategory.obj K ⟶
      K :=
  (geometricFrobeniusDerivedIso X).hom.app K

/-- The comparison `c_K` is the forward component of `geometricFrobeniusDerivedIso`. -/
theorem geometricFrobeniusComparison_spec
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    geometricFrobeniusComparison X K =
      (geometricFrobeniusDerivedIso X).hom.app K :=
  rfl

/-- Derived restriction of `K` to the geometric fibre, as inverse image along
`FieldExtension.toSource`. -/
def geometricRestrictionDerived
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    DerivedCategory (Sheaf (geometricFibre X).smallEtaleTopology (ModuleCat.{u} Λ)) :=
  (Sheaf.smallEtaleInverseImage (FieldExtension.toSource k (AlgebraicClosure k) X.hom) (ModuleCat.{u} Λ)).mapDerivedCategory.obj K

/-- Unfolding of derived geometric restriction as `mapDerivedCategory` of module
sheaf pullback along `X_k̄ ⟶ X`. -/
theorem geometricRestrictionDerived_eq
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    geometricRestrictionDerived X K =
      (Sheaf.smallEtaleInverseImage (FieldExtension.toSource k (AlgebraicClosure k) X.hom) (ModuleCat.{u} Λ)).mapDerivedCategory.obj K :=
  rfl

/-- Two-step identification `((π_X)_{k̄})⁻¹(F|_{X_k̄}) ≅ (π_X⁻¹ F)|_{X_k̄} ≅
F|_{X_k̄}` of sheaves of left `Λ`-modules. -/
def geometricFrobeniusModuleRestrictionIso :
    Sheaf.smallEtaleInverseImage (FieldExtension.toSource k (AlgebraicClosure k) X.hom) (ModuleCat.{u} Λ) ⋙
        Sheaf.smallEtaleInverseImage (geometricFrobeniusBaseChange X) (ModuleCat.{u} Λ) ≅
      Sheaf.smallEtaleInverseImage (FieldExtension.toSource k (AlgebraicClosure k) X.hom) (ModuleCat.{u} Λ) :=
  etaleModuleSheafPullback_comp Λ
      (FieldExtension.toSource k (AlgebraicClosure k) X.hom)
      (geometricFrobeniusBaseChange X) ≪≫
    etaleModuleSheafPullback_congr Λ (geometricFrobeniusBaseChange_comp_toSource X) ≪≫
      (etaleModuleSheafPullback_comp Λ (geometricFrobenius_ofFiniteField X)
          (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).symm ≪≫
        isoWhiskerRight (geometricFrobeniusModuleIso X)
            (Sheaf.smallEtaleInverseImage (FieldExtension.toSource k (AlgebraicClosure k) X.hom) (ModuleCat.{u} Λ)) ≪≫
          leftUnitor _

/-- Bundled exact-functor isomorphism underlying
`geometricFrobeniusModuleRestrictionIso`. -/
def geometricFrobeniusRestrictionExactIso :
    ExactFunctor.of
        (Sheaf.smallEtaleInverseImage (FieldExtension.toSource k (AlgebraicClosure k) X.hom) (ModuleCat.{u} Λ) ⋙
          Sheaf.smallEtaleInverseImage (geometricFrobeniusBaseChange X) (ModuleCat.{u} Λ)) ≅
      ExactFunctor.of
        (Sheaf.smallEtaleInverseImage (FieldExtension.toSource k (AlgebraicClosure k) X.hom) (ModuleCat.{u} Λ)) :=
  ObjectProperty.isoMk _ (geometricFrobeniusModuleRestrictionIso X)

/-- Derived two-step identification `((π_X)_{k̄})⁻¹(K|_{X_k̄}) ≅ K|_{X_k̄}`. -/
def geometricFrobeniusRestrictionDerivedIso
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (Sheaf.smallEtaleInverseImage (geometricFrobeniusBaseChange X) (ModuleCat.{u} Λ)).mapDerivedCategory.obj
        (geometricRestrictionDerived X K) ≅
      geometricRestrictionDerived X K :=
  ((ExactFunctor.MapDerivedCategory.compFunctorIso
          (ExactFunctor.of
            (Sheaf.smallEtaleInverseImage (FieldExtension.toSource k (AlgebraicClosure k) X.hom) (ModuleCat.{u} Λ)))
          (ExactFunctor.of
            (Sheaf.smallEtaleInverseImage (geometricFrobeniusBaseChange X) (ModuleCat.{u} Λ)))).symm ≪≫
      ExactFunctor.MapDerivedCategory.mapIso
        (geometricFrobeniusRestrictionExactIso X)).app K

/-- Derived global sections `RΓ(X_k̄, -)` of sheaves of left `Λ`-modules on the
geometric fibre. -/
abbrev geometricRGammaFunctor :
    DerivedCategory (Sheaf (geometricFibre X).smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
      DerivedCategory (ModuleCat.{u} Λ) :=
  etaleModuleDerivedGamma Λ (geometricFibre X)

/-- Derived global sections `RΓ(X_k̄, K|_{X_k̄})`. -/
def geometricRGamma
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    DerivedCategory (ModuleCat.{u} Λ) :=
  (geometricRGammaFunctor X).obj (geometricRestrictionDerived X K)

/-- Unfolding of `geometricRGamma` as the cochain-level total right derived functor
of sections at the identity étale object of `X_k̄`. -/
theorem geometricRGamma_eq
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    geometricRGamma X K =
      (geometricRGammaFunctor X).obj (geometricRestrictionDerived X K) :=
  rfl

/-- Pullback of derived global sections along `(π_X)_{k̄}`, landing in `RΓ` of
the inverse image. -/
def geometricRGammaPullback :
    geometricRGammaFunctor X ⟶
      (Sheaf.smallEtaleInverseImage (geometricFrobeniusBaseChange X) (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
        geometricRGammaFunctor X :=
  (geometricRGammaFunctor X).rightDerivedDesc
    (RightDerived.Cochain.unit (etaleModuleGamma Λ (geometricFibre X)))
    (@HomologicalComplex.quasiIso ℤ
      (Sheaf (geometricFibre X).smallEtaleTopology (ModuleCat.{u} Λ)) _
      (@Preadditive.preadditiveHasZeroMorphisms _ _ Abelian.toPreadditive)
      (up ℤ) inferInstance)
    ((Sheaf.smallEtaleInverseImage (geometricFrobeniusBaseChange X) (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
      geometricRGammaFunctor X)
    (whiskerRight
        (@NatTrans.mapHomologicalComplex ℤ _ _ _ _
          (@Preadditive.preadditiveHasZeroMorphisms _ _ Abelian.toPreadditive)
          inferInstance _ _ inferInstance inferInstance
          (etaleModuleGammaPullback Λ (geometricFrobeniusBaseChange X)) (up ℤ))
        DerivedCategory.Q ≫
      RightDerived.Cochain.ExactFirst.unit
        (ExactFunctor.of (Sheaf.smallEtaleInverseImage (geometricFrobeniusBaseChange X) (ModuleCat.{u} Λ)))
        (etaleModuleGamma Λ (geometricFibre X)))

/-- Geometric Frobenius pullback `π_X^*` on `RΓ(X_k̄, K|_{X_k̄})`. -/
def geometricFrobeniusRGamma
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    geometricRGamma X K ⟶ geometricRGamma X K :=
  (geometricRGammaPullback X).app (geometricRestrictionDerived X K) ≫
    (geometricRGammaFunctor X).map (geometricFrobeniusRestrictionDerivedIso X K).hom

/-- Unfolding of `π_X^*` as derived sections-pullback along `(π_X)_{k̄}` followed
by the two-step coefficient identification. -/
theorem geometricFrobeniusRGamma_spec
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    geometricFrobeniusRGamma X K =
      (geometricRGammaPullback X).app (geometricRestrictionDerived X K) ≫
        (geometricRGammaFunctor X).map
          (geometricFrobeniusRestrictionDerivedIso X K).hom :=
  rfl

end AlgebraicGeometry.SchemeOverField
