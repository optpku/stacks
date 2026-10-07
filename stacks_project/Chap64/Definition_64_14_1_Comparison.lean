module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain.ExactFirst
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import stacks_project.Chap59.Lemma_59_39_1
public import stacks_project.Chap64.Theorem_64_3_9_Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Geometric Frobenius comparison on derived étale module sheaves

This leaf owns the ModuleCat-valued comparison `c_K : π_X⁻¹ K ⟶ K`, geometric
restriction of derived objects to `X_k̄`, derived global sections
`RΓ(X_k̄, K|_{X_k̄})`, and the induced action `π_X^*` on that perfect complex.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open Opposite ComplexShape
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

/-- Inverse image of a small-étale sheaf of left `Λ`-modules along a morphism of
schemes. -/
abbrev etaleModuleSheafPullback (Λ : Type u) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ) :=
  (smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
    Y.smallEtaleTopology X.smallEtaleTopology

/-- Inverse image of module sheaves along a morphism of schemes is sheaf pullback
along `smallEtalePullback`. -/
theorem etaleModuleSheafPullback_eq (Λ : Type u) [Ring Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    etaleModuleSheafPullback Λ f =
      (smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
        Y.smallEtaleTopology X.smallEtaleTopology :=
  sorry

/-- Inverse-image identification along equal morphisms, by substitution of the
morphism equality. -/
def etaleModuleSheafPullback_congr (Λ : Type u) [Ring Λ] {A B : Scheme.{u}}
    {p q : A ⟶ B} (h : p = q)
    [HasWeakSheafify A.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback p).op.HasLeftKanExtension P]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback q).op.HasLeftKanExtension P] :
    etaleModuleSheafPullback Λ p ≅ etaleModuleSheafPullback Λ q :=
  h ▸ Iso.refl _

/-- Pullback of module sheaves along a composite is the composite pullback. -/
def etaleModuleSheafPullback_comp (Λ : Type u) [Ring Λ] {A B C : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B)
    [HasWeakSheafify B.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasWeakSheafify C.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : A.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback p).op.HasLeftKanExtension P]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback q).op.HasLeftKanExtension P]
    [∀ P : A.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (q ≫ p)).op.HasLeftKanExtension P] :
    etaleModuleSheafPullback Λ p ⋙ etaleModuleSheafPullback Λ q ≅
      etaleModuleSheafPullback Λ (q ≫ p) :=
  let siteIso :
      smallEtalePullback p ⋙ smallEtalePullback q ≅ smallEtalePullback (q ≫ p) :=
    (MorphismProperty.Over.pullbackComp q p).symm
  Adjunction.leftAdjointCompIso
    ((smallEtalePullback p).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
      A.smallEtaleTopology B.smallEtaleTopology)
    ((smallEtalePullback q).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
      B.smallEtaleTopology C.smallEtaleTopology)
    ((smallEtalePullback (q ≫ p)).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
      A.smallEtaleTopology C.smallEtaleTopology)
    (sheafPushforwardContinuousComp' siteIso (ModuleCat.{u} Λ)
      A.smallEtaleTopology B.smallEtaleTopology C.smallEtaleTopology)

/-- Global sections of a sheaf of left `Λ`-modules at the identity étale object. -/
abbrev etaleModuleGamma (Λ : Type u) [Ring Λ] (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ) ⥤ ModuleCat.{u} Λ :=
  (sheafSections X.smallEtaleTopology (ModuleCat.{u} Λ)).obj (op (globalEtale X))

/-- Unfolding of module-valued global sections at the identity étale object. -/
theorem etaleModuleGamma_eq (Λ : Type u) [Ring Λ] (X : Scheme.{u}) :
    etaleModuleGamma Λ X =
      (sheafSections X.smallEtaleTopology (ModuleCat.{u} Λ)).obj (op (globalEtale X)) :=
  sorry

/-- Inverse image of sheaves of left `Λ`-modules is additive. -/
instance instAdditive_etaleModuleSheafPullback (Λ : Type u) [Ring Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    @Functor.Additive
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))
      (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) _ _
      Abelian.toPreadditive Abelian.toPreadditive
      (etaleModuleSheafPullback Λ f) :=
  sorry

/-- Inverse image of sheaves of left `Λ`-modules preserves finite limits. -/
instance instPreservesFiniteLimits_etaleModuleSheafPullback (Λ : Type u) [Ring Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    PreservesFiniteLimits (etaleModuleSheafPullback Λ f) :=
  sorry

/-- Inverse image of sheaves of left `Λ`-modules preserves finite colimits. -/
instance instPreservesFiniteColimits_etaleModuleSheafPullback (Λ : Type u) [Ring Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    PreservesFiniteColimits (etaleModuleSheafPullback Λ f) :=
  sorry

/-- The small-étale category of sheaves of left `Λ`-modules has homology. -/
instance instCategoryWithHomology_etaleModuleSheaf (Λ : Type u) [Ring Λ]
    (X : Scheme.{u})
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))] :
    CategoryWithHomology (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  sorry

/-- Preadditive structure on étale `Λ`-module sheaves, aligned with the abelian
instance rather than the full-subcategory instance. -/
instance (priority := 10000) instPreadditive_etaleModuleSheaf
    (Λ : Type u) [Ring Λ] (X : Scheme.{u})
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))] :
    Preadditive (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  Abelian.toPreadditive

/-- Preadditive structure on left `Λ`-modules, aligned with the abelian
instance rather than `ModuleCat.instPreadditive`. -/
instance (priority := 10000) instPreadditive_moduleCat (Λ : Type u) [Ring Λ] :
    Preadditive (ModuleCat.{u} Λ) :=
  Abelian.toPreadditive

/-- Zero morphisms on étale `Λ`-module sheaves, aligned with `Abelian.toPreadditive`. -/
instance (priority := 10000) instHasZeroMorphisms_etaleModuleSheaf
    (Λ : Type u) [Ring Λ] (X : Scheme.{u})
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))] :
    HasZeroMorphisms (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  @Preadditive.preadditiveHasZeroMorphisms _ _ Abelian.toPreadditive

/-- Zero morphisms on left `Λ`-modules, aligned with `Abelian.toPreadditive`. -/
instance (priority := 10000) instHasZeroMorphisms_moduleCat (Λ : Type u) [Ring Λ] :
    HasZeroMorphisms (ModuleCat.{u} Λ) :=
  @Preadditive.preadditiveHasZeroMorphisms _ _ Abelian.toPreadditive

/-- Global sections of sheaves of left `Λ`-modules are additive. -/
instance instAdditive_etaleModuleGamma (Λ : Type u) [Ring Λ] (X : Scheme.{u})
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))] :
    (etaleModuleGamma Λ X).Additive :=
  sorry

/-- Global sections of sheaves of left `Λ`-modules are additive with respect to
the `Abelian.toPreadditive` instances on source and target. -/
instance instAdditive_etaleModuleGamma_abelian (Λ : Type u) [Ring Λ] (X : Scheme.{u})
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [Abelian (ModuleCat.{u} Λ)] :
    @Functor.Additive
      (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
      (ModuleCat.{u} Λ) _ _
      Abelian.toPreadditive Abelian.toPreadditive
      (etaleModuleGamma Λ X) :=
  sorry

/-- Global sections of sheaves of left `Λ`-modules admit a total right derived
functor on cochain complexes. -/
instance instHasRightDerivedFunctor_etaleModuleGamma (Λ : Type u) [Ring Λ]
    (X : Scheme.{u})
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (ModuleCat.{u} Λ)] :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModuleGamma Λ X))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (up ℤ)) :=
  sorry

/-- Pullback of underived global sections along inverse image of module sheaves. -/
def etaleModuleGammaPullback (Λ : Type u) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    etaleModuleGamma Λ Y ⟶
      etaleModuleSheafPullback Λ f ⋙ etaleModuleGamma Λ X where
  app F :=
    ((sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)).map
        (((smallEtalePullback f).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
            Y.smallEtaleTopology X.smallEtaleTopology).unit.app F)).app
      (op (globalEtale Y)) ≫
      ((etaleModuleSheafPullback Λ f).obj F).obj.map
        (op (globalEtalePullbackIso f).inv)
  naturality := fun _ _ _ ↦ sorry

/-- Component of the underived global-sections pullback at a sheaf, as the
adjunction unit followed by the identification of terminal étale objects. -/
theorem etaleModuleGammaPullback_app (Λ : Type u) [Ring Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (etaleModuleGammaPullback Λ f).app F =
      ((sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)).map
          (((smallEtalePullback f).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
              Y.smallEtaleTopology X.smallEtaleTopology).unit.app F)).app
        (op (globalEtale Y)) ≫
        ((etaleModuleSheafPullback Λ f).obj F).obj.map
          (op (globalEtalePullbackIso f).inv) :=
  sorry

/-- Derived étale global sections `RΓ(X, -)` of sheaves of left `Λ`-modules. -/
abbrev etaleModuleDerivedGamma (Λ : Type u) [Ring Λ] (X : Scheme.{u})
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (ModuleCat.{u} Λ)] :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
      DerivedCategory (ModuleCat.{u} Λ) :=
  RightDerived.Cochain.functor (etaleModuleGamma Λ X)

/-- `RΓ(X, -)` is the cochain-level total right derived functor of étale module
sections at `globalEtale X`. -/
theorem etaleModuleDerivedGamma_spec (Λ : Type u) [Ring Λ] (X : Scheme.{u})
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (ModuleCat.{u} Λ)] :
    etaleModuleDerivedGamma Λ X =
      RightDerived.Cochain.functor (etaleModuleGamma Λ X) :=
  sorry

end AlgebraicGeometry.Scheme.Hom

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
  sorry

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
    etaleModuleSheafPullback Λ (geometricFrobenius_ofFiniteField X) ≅
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
  sorry

/-- Inverse image along geometric Frobenius is additive, via the identification
with the identity functor. -/
instance instAdditive_geometricFrobeniusModulePullback :
    (etaleModuleSheafPullback Λ (geometricFrobenius_ofFiniteField X)).Additive :=
  Functor.additive_of_iso (geometricFrobeniusModuleIso X).symm

/-- Inverse image along geometric Frobenius preserves finite limits. -/
instance instPreservesFiniteLimits_geometricFrobeniusModulePullback :
    PreservesFiniteLimits
      (etaleModuleSheafPullback Λ (geometricFrobenius_ofFiniteField X)) :=
  preservesFiniteLimits_of_natIso (geometricFrobeniusModuleIso X).symm

/-- Inverse image along geometric Frobenius preserves finite colimits. -/
instance instPreservesFiniteColimits_geometricFrobeniusModulePullback :
    PreservesFiniteColimits
      (etaleModuleSheafPullback Λ (geometricFrobenius_ofFiniteField X)) :=
  preservesFiniteColimits_of_natIso (geometricFrobeniusModuleIso X).symm

/-- Inverse image along `X_k̄ ⟶ X` is additive. -/
instance instAdditive_geometricRestrictionPullback :
    (etaleModuleSheafPullback Λ
        (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).Additive :=
  sorry

/-- Inverse image along `X_k̄ ⟶ X` preserves finite limits. -/
instance instPreservesFiniteLimits_geometricRestrictionPullback :
    PreservesFiniteLimits
      (etaleModuleSheafPullback Λ
        (FieldExtension.toSource k (AlgebraicClosure k) X.hom)) :=
  sorry

/-- Inverse image along `X_k̄ ⟶ X` preserves finite colimits. -/
instance instPreservesFiniteColimits_geometricRestrictionPullback :
    PreservesFiniteColimits
      (etaleModuleSheafPullback Λ
        (FieldExtension.toSource k (AlgebraicClosure k) X.hom)) :=
  sorry

/-- Inverse image along `(π_X)_{k̄}` is additive. -/
instance instAdditive_geometricFrobeniusBaseChangePullback :
    (etaleModuleSheafPullback Λ (geometricFrobeniusBaseChange X)).Additive :=
  sorry

/-- Inverse image along `(π_X)_{k̄}` preserves finite limits. -/
instance instPreservesFiniteLimits_geometricFrobeniusBaseChangePullback :
    PreservesFiniteLimits
      (etaleModuleSheafPullback Λ (geometricFrobeniusBaseChange X)) :=
  sorry

/-- Inverse image along `(π_X)_{k̄}` preserves finite colimits. -/
instance instPreservesFiniteColimits_geometricFrobeniusBaseChangePullback :
    PreservesFiniteColimits
      (etaleModuleSheafPullback Λ (geometricFrobeniusBaseChange X)) :=
  sorry

/-- Global sections on the geometric fibre are additive. -/
instance instAdditive_geometricFibreGamma :
    (etaleModuleGamma Λ (geometricFibre X)).Additive :=
  sorry

/-- Global sections on the geometric fibre are additive with respect to
the `Abelian.toPreadditive` instances. -/
instance instAdditive_geometricFibreGamma_abelian :
    @Functor.Additive
      (Sheaf (geometricFibre X).smallEtaleTopology (ModuleCat.{u} Λ))
      (ModuleCat.{u} Λ) _ _
      Abelian.toPreadditive Abelian.toPreadditive
      (etaleModuleGamma Λ (geometricFibre X)) :=
  sorry

/-- Derived global sections on the geometric fibre exist as a total right
derived functor. -/
instance instHasRightDerivedFunctor_geometricFibreGamma :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModuleGamma Λ (geometricFibre X)))
      (HomologicalComplex.quasiIso
        (Sheaf (geometricFibre X).smallEtaleTopology (ModuleCat.{u} Λ)) (up ℤ)) :=
  sorry


/-- Bundled exact-functor isomorphism underlying `geometricFrobeniusModuleIso`. -/
def geometricFrobeniusExactIso :
    ExactFunctor.of (etaleModuleSheafPullback Λ (geometricFrobenius_ofFiniteField X)) ≅
      ExactFunctor.id (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) where
  hom := ⟨(geometricFrobeniusModuleIso X).hom⟩
  inv := ⟨(geometricFrobeniusModuleIso X).inv⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Derived identification `π_X⁻¹ K ≅ K` induced by the sheaf-level geometric
Frobenius iso. -/
def geometricFrobeniusDerivedIso :
    (etaleModuleSheafPullback Λ (geometricFrobenius_ofFiniteField X)).mapDerivedCategory ≅
      𝟭 (DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :=
  ExactFunctor.MapDerivedCategory.mapIso (geometricFrobeniusExactIso X) ≪≫
    ExactFunctor.MapDerivedCategory.idFunctorIso _

/-- Canonical comparison `c_K : π_X⁻¹ K ⟶ K` on derived étale sheaves of left
`Λ`-modules. -/
def geometricFrobeniusComparison
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleModuleSheafPullback Λ (geometricFrobenius_ofFiniteField X)).mapDerivedCategory.obj K ⟶
      K :=
  (geometricFrobeniusDerivedIso X).hom.app K

/-- The comparison `c_K` is the forward component of `geometricFrobeniusDerivedIso`. -/
theorem geometricFrobeniusComparison_spec
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    geometricFrobeniusComparison X K =
      (geometricFrobeniusDerivedIso X).hom.app K :=
  sorry

/-- Derived restriction of `K` to the geometric fibre, as inverse image along
`FieldExtension.toSource`. -/
def geometricRestrictionDerived
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    DerivedCategory (Sheaf (geometricFibre X).smallEtaleTopology (ModuleCat.{u} Λ)) :=
  (etaleModuleSheafPullback Λ
      (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).mapDerivedCategory.obj K

/-- Unfolding of derived geometric restriction as `mapDerivedCategory` of module
sheaf pullback along `X_k̄ ⟶ X`. -/
theorem geometricRestrictionDerived_eq
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    geometricRestrictionDerived X K =
      (etaleModuleSheafPullback Λ
          (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).mapDerivedCategory.obj K :=
  sorry

/-- Two-step identification `((π_X)_{k̄})⁻¹(F|_{X_k̄}) ≅ (π_X⁻¹ F)|_{X_k̄} ≅
F|_{X_k̄}` of sheaves of left `Λ`-modules. -/
def geometricFrobeniusModuleRestrictionIso :
    etaleModuleSheafPullback Λ
          (FieldExtension.toSource k (AlgebraicClosure k) X.hom) ⋙
        etaleModuleSheafPullback Λ (geometricFrobeniusBaseChange X) ≅
      etaleModuleSheafPullback Λ
        (FieldExtension.toSource k (AlgebraicClosure k) X.hom) :=
  etaleModuleSheafPullback_comp Λ
      (FieldExtension.toSource k (AlgebraicClosure k) X.hom)
      (geometricFrobeniusBaseChange X) ≪≫
    etaleModuleSheafPullback_congr Λ (geometricFrobeniusBaseChange_comp_toSource X) ≪≫
      (etaleModuleSheafPullback_comp Λ (geometricFrobenius_ofFiniteField X)
          (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).symm ≪≫
        isoWhiskerRight (geometricFrobeniusModuleIso X)
            (etaleModuleSheafPullback Λ
              (FieldExtension.toSource k (AlgebraicClosure k) X.hom)) ≪≫
          leftUnitor _

/-- Bundled exact-functor isomorphism underlying
`geometricFrobeniusModuleRestrictionIso`. -/
def geometricFrobeniusRestrictionExactIso :
    ExactFunctor.of
        (etaleModuleSheafPullback Λ
            (FieldExtension.toSource k (AlgebraicClosure k) X.hom) ⋙
          etaleModuleSheafPullback Λ (geometricFrobeniusBaseChange X)) ≅
      ExactFunctor.of
        (etaleModuleSheafPullback Λ
          (FieldExtension.toSource k (AlgebraicClosure k) X.hom)) where
  hom := ⟨(geometricFrobeniusModuleRestrictionIso X).hom⟩
  inv := ⟨(geometricFrobeniusModuleRestrictionIso X).inv⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Derived two-step identification `((π_X)_{k̄})⁻¹(K|_{X_k̄}) ≅ K|_{X_k̄}`. -/
def geometricFrobeniusRestrictionDerivedIso
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleModuleSheafPullback Λ (geometricFrobeniusBaseChange X)).mapDerivedCategory.obj
        (geometricRestrictionDerived X K) ≅
      geometricRestrictionDerived X K :=
  ((ExactFunctor.MapDerivedCategory.compFunctorIso
          (ExactFunctor.of
            (etaleModuleSheafPullback Λ
              (FieldExtension.toSource k (AlgebraicClosure k) X.hom)))
          (ExactFunctor.of
            (etaleModuleSheafPullback Λ (geometricFrobeniusBaseChange X)))).symm ≪≫
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
  sorry

/-- Pullback of derived global sections along `(π_X)_{k̄}`, landing in `RΓ` of
the inverse image. -/
def geometricRGammaPullback :
    geometricRGammaFunctor X ⟶
      (etaleModuleSheafPullback Λ (geometricFrobeniusBaseChange X)).mapDerivedCategory ⋙
        geometricRGammaFunctor X :=
  (geometricRGammaFunctor X).rightDerivedDesc
    (RightDerived.Cochain.unit (etaleModuleGamma Λ (geometricFibre X)))
    (HomologicalComplex.quasiIso
      (Sheaf (geometricFibre X).smallEtaleTopology (ModuleCat.{u} Λ)) (up ℤ))
    ((etaleModuleSheafPullback Λ (geometricFrobeniusBaseChange X)).mapDerivedCategory ⋙
      geometricRGammaFunctor X)
    (whiskerRight
        (NatTrans.mapHomologicalComplex
          (etaleModuleGammaPullback Λ (geometricFrobeniusBaseChange X)) (up ℤ))
        DerivedCategory.Q ≫
      RightDerived.Cochain.ExactFirst.unit
        (ExactFunctor.of (etaleModuleSheafPullback Λ (geometricFrobeniusBaseChange X)))
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
  sorry

end AlgebraicGeometry.SchemeOverField
