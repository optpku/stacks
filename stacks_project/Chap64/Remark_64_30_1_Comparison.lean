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
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import stacks_project.Chap59.Lemma_59_39_1
public import stacks_project.Chap64.Proposition_64_10_2_Trace
public import stacks_project.Chap64.Remark_64_29_2_Sheaf
public import stacks_project.Chap64.Remark_64_30_1_Extension
public import stacks_project.Chap64.Theorem_64_3_9_Pullback

/-!
# Geometric Frobenius on derived sections of `π₁`-modules

This leaf owns the `ModuleCat.{u+1}` comparison used by locally constant sheaves
`F_ρ`: inverse image of module sheaves, `RΓ(X_k̄, -)`, and the geometric
Frobenius pullback `π_X^*`. It is the coefficient-universe lift of
`Definition_64_14_1_Comparison` needed to apply those maps to
`sheafOfPi1Module`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open Opposite ComplexShape ProfiniteGrp
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

/-- Inverse image of a small-étale sheaf of left `Λ`-modules along a morphism of
schemes, for coefficients in `Type (u + 1)`. -/
abbrev etaleModuleSheafPullback (Λ : Type (u + 1)) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
    Y.smallEtaleTopology X.smallEtaleTopology

/-- Inverse image of module sheaves is sheaf pullback along `smallEtalePullback`. -/
theorem etaleModuleSheafPullback_eq (Λ : Type (u + 1)) [Ring Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    etaleModuleSheafPullback Λ f =
      (smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
        Y.smallEtaleTopology X.smallEtaleTopology :=
  sorry

/-- Inverse-image identification along equal morphisms. -/
def etaleModuleSheafPullback_congr (Λ : Type (u + 1)) [Ring Λ] {A B : Scheme.{u}}
    {p q : A ⟶ B} (h : p = q)
    [HasWeakSheafify A.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback p).op.HasLeftKanExtension P]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback q).op.HasLeftKanExtension P] :
    etaleModuleSheafPullback Λ p ≅ etaleModuleSheafPullback Λ q :=
  h ▸ Iso.refl _

/-- Pullback of module sheaves along a composite is the composite pullback. -/
def etaleModuleSheafPullback_comp (Λ : Type (u + 1)) [Ring Λ] {A B C : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B)
    [HasWeakSheafify B.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [HasWeakSheafify C.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ P : A.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback p).op.HasLeftKanExtension P]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback q).op.HasLeftKanExtension P]
    [∀ P : A.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback (q ≫ p)).op.HasLeftKanExtension P] :
    etaleModuleSheafPullback Λ p ⋙ etaleModuleSheafPullback Λ q ≅
      etaleModuleSheafPullback Λ (q ≫ p) :=
  let siteIso :
      smallEtalePullback p ⋙ smallEtalePullback q ≅ smallEtalePullback (q ≫ p) :=
    (MorphismProperty.Over.pullbackComp q p).symm
  Adjunction.leftAdjointCompIso
    ((smallEtalePullback p).sheafAdjunctionContinuous (ModuleCat.{u + 1} Λ)
      A.smallEtaleTopology B.smallEtaleTopology)
    ((smallEtalePullback q).sheafAdjunctionContinuous (ModuleCat.{u + 1} Λ)
      B.smallEtaleTopology C.smallEtaleTopology)
    ((smallEtalePullback (q ≫ p)).sheafAdjunctionContinuous (ModuleCat.{u + 1} Λ)
      A.smallEtaleTopology C.smallEtaleTopology)
    (sheafPushforwardContinuousComp' siteIso (ModuleCat.{u + 1} Λ)
      A.smallEtaleTopology B.smallEtaleTopology C.smallEtaleTopology)

/-- Global sections of a sheaf of left `Λ`-modules at the identity étale object. -/
abbrev etaleModuleGamma (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ ModuleCat.{u + 1} Λ :=
  (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op (globalEtale X))

/-- Unfolding of module-valued global sections at the identity étale object. -/
theorem etaleModuleGamma_eq (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u}) :
    etaleModuleGamma Λ X =
      (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op (globalEtale X)) :=
  sorry

/-- Inverse image of sheaves of left `Λ`-modules is additive. -/
instance instAdditive_etaleModuleSheafPullback (Λ : Type (u + 1)) [Ring Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
    [Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    @Functor.Additive
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) _ _
      Abelian.toPreadditive Abelian.toPreadditive
      (etaleModuleSheafPullback Λ f) :=
  sorry

/-- Inverse image of sheaves of left `Λ`-modules preserves finite limits. -/
instance instPreservesFiniteLimits_etaleModuleSheafPullback (Λ : Type (u + 1)) [Ring Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
    [Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    PreservesFiniteLimits (etaleModuleSheafPullback Λ f) :=
  sorry

/-- Inverse image of sheaves of left `Λ`-modules preserves finite colimits. -/
instance instPreservesFiniteColimits_etaleModuleSheafPullback (Λ : Type (u + 1)) [Ring Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
    [Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    PreservesFiniteColimits (etaleModuleSheafPullback Λ f) :=
  sorry

/-- Preadditive structure on étale `Λ`-module sheaves, aligned with the abelian instance. -/
instance (priority := 10000) instPreadditive_etaleModuleSheaf
    (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u})
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))] :
    Preadditive (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  Abelian.toPreadditive

/-- Preadditive structure on left `Λ`-modules, aligned with the abelian instance. -/
instance (priority := 10000) instPreadditive_moduleCat (Λ : Type (u + 1)) [Ring Λ] :
    Preadditive (ModuleCat.{u + 1} Λ) :=
  Abelian.toPreadditive

/-- Zero morphisms on étale `Λ`-module sheaves, aligned with `Abelian.toPreadditive`. -/
instance (priority := 10000) instHasZeroMorphisms_etaleModuleSheaf
    (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u})
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))] :
    HasZeroMorphisms (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  @Preadditive.preadditiveHasZeroMorphisms _ _ Abelian.toPreadditive

/-- Zero morphisms on left `Λ`-modules, aligned with `Abelian.toPreadditive`. -/
instance (priority := 10000) instHasZeroMorphisms_moduleCat (Λ : Type (u + 1)) [Ring Λ] :
    HasZeroMorphisms (ModuleCat.{u + 1} Λ) :=
  @Preadditive.preadditiveHasZeroMorphisms _ _ Abelian.toPreadditive

/-- Global sections of sheaves of left `Λ`-modules are additive. -/
instance instAdditive_etaleModuleGamma (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u})
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))] :
    (etaleModuleGamma Λ X).Additive :=
  sorry

/-- Global sections of sheaves of left `Λ`-modules are additive with respect to
the `Abelian.toPreadditive` instances on source and target. -/
instance instAdditive_etaleModuleGamma_abelian (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u})
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
    [Abelian (ModuleCat.{u + 1} Λ)] :
    @Functor.Additive
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (ModuleCat.{u + 1} Λ) _ _
      Abelian.toPreadditive Abelian.toPreadditive
      (etaleModuleGamma Λ X) :=
  sorry

/-- Global sections of sheaves of left `Λ`-modules admit a total right derived
functor on cochain complexes. -/
instance instHasRightDerivedFunctor_etaleModuleGamma (Λ : Type (u + 1)) [Ring Λ]
    (X : Scheme.{u})
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))] :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModuleGamma Λ X))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (up ℤ)) :=
  sorry

/-- Pullback of underived global sections along inverse image of module sheaves. -/
def etaleModuleGammaPullback (Λ : Type (u + 1)) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    etaleModuleGamma Λ Y ⟶
      etaleModuleSheafPullback Λ f ⋙ etaleModuleGamma Λ X where
  app F :=
    ((sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
        (((smallEtalePullback f).sheafAdjunctionContinuous (ModuleCat.{u + 1} Λ)
            Y.smallEtaleTopology X.smallEtaleTopology).unit.app F)).app
      (op (globalEtale Y)) ≫
      ((etaleModuleSheafPullback Λ f).obj F).obj.map
        (op (globalEtalePullbackIso f).inv)
  naturality := fun _ _ _ ↦ sorry

/-- The underived global-sections pullback is the adjunction unit followed by the
identification of terminal étale objects. -/
theorem etaleModuleGammaPullback_app (Λ : Type (u + 1)) [Ring Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (etaleModuleGammaPullback Λ f).app F =
      ((sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
          (((smallEtalePullback f).sheafAdjunctionContinuous (ModuleCat.{u + 1} Λ)
              Y.smallEtaleTopology X.smallEtaleTopology).unit.app F)).app
        (op (globalEtale Y)) ≫
        ((etaleModuleSheafPullback Λ f).obj F).obj.map
          (op (globalEtalePullbackIso f).inv) :=
  sorry

/-- Derived étale global sections `RΓ(X, -)` of sheaves of left `Λ`-modules. -/
abbrev etaleModuleDerivedGamma (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u})
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))] :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (ModuleCat.{u + 1} Λ) :=
  RightDerived.Cochain.functor (etaleModuleGamma Λ X)

/-- `RΓ(X, -)` is the cochain-level total right derived functor of étale module
sections at `globalEtale X`. -/
theorem etaleModuleDerivedGamma_spec (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u})
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))] :
    etaleModuleDerivedGamma Λ X = RightDerived.Cochain.functor (etaleModuleGamma Λ X) :=
  sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.SchemeOverField

open AlgebraicGeometry.Scheme.Hom
open CategoryTheory.Action.ModuleCat
open CategoryTheory.ObjectProperty

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {Λ : Type (u + 1)} [Ring Λ]
variable (X : SchemeOverField k)
variable [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [Abelian (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [Abelian (Sheaf (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [HasDerivedCategory
    (Sheaf (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback (geometricFrobenius_ofFiniteField X)).op.HasLeftKanExtension P]
variable [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback
        (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).op.HasLeftKanExtension P]
variable [∀ P : (geometricBaseChange X).Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback (geometricFrobeniusBaseChange X)).op.HasLeftKanExtension P]
variable [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback
        (geometricFrobeniusBaseChange X ≫
          FieldExtension.toSource k (AlgebraicClosure k) X.hom)).op.HasLeftKanExtension P]
variable [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback
        (FieldExtension.toSource k (AlgebraicClosure k) X.hom ≫
          geometricFrobenius_ofFiniteField X)).op.HasLeftKanExtension P]

/-- Canonical identification `π_X⁻¹ F ≅ F` of sheaves of left `Λ`-modules, induced
by the small-étale site isomorphism of geometric Frobenius. -/
def geometricFrobeniusModuleIso :
    etaleModuleSheafPullback Λ (geometricFrobenius_ofFiniteField X) ≅
      𝟭 (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  Adjunction.leftAdjointUniq
    ((smallEtalePullback (geometricFrobenius_ofFiniteField X)).sheafAdjunctionContinuous
      (ModuleCat.{u + 1} Λ) X.left.smallEtaleTopology X.left.smallEtaleTopology)
    (Adjunction.id.ofNatIsoRight
      (sheafPushforwardContinuousId'
        (geometricFrobenius_smallEtalePullbackIso X).symm (ModuleCat.{u + 1} Λ)
        X.left.smallEtaleTopology).symm)

/-- The sheaf-level geometric Frobenius identification is left-adjoint uniqueness
for the site isomorphism `𝟭 ≅ smallEtalePullback π_X`. -/
theorem geometricFrobeniusModuleIso_spec :
    geometricFrobeniusModuleIso X =
      Adjunction.leftAdjointUniq
        ((smallEtalePullback (geometricFrobenius_ofFiniteField X)).sheafAdjunctionContinuous
          (ModuleCat.{u + 1} Λ) X.left.smallEtaleTopology X.left.smallEtaleTopology)
        (Adjunction.id.ofNatIsoRight
          (sheafPushforwardContinuousId'
            (geometricFrobenius_smallEtalePullbackIso X).symm (ModuleCat.{u + 1} Λ)
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
    (etaleModuleGamma Λ (geometricBaseChange X)).Additive :=
  sorry

/-- Global sections on the geometric fibre are additive with respect to
the `Abelian.toPreadditive` instances. -/
instance instAdditive_geometricFibreGamma_abelian :
    @Functor.Additive
      (Sheaf (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (ModuleCat.{u + 1} Λ) _ _
      Abelian.toPreadditive Abelian.toPreadditive
      (etaleModuleGamma Λ (geometricBaseChange X)) :=
  sorry

/-- Derived global sections on the geometric fibre exist as a total right
derived functor. -/
instance instHasRightDerivedFunctor_geometricFibreGamma :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModuleGamma Λ (geometricBaseChange X)))
      (HomologicalComplex.quasiIso
        (Sheaf (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ)) (up ℤ)) :=
  sorry

/-- Bundled exact-functor isomorphism underlying `geometricFrobeniusModuleIso`. -/
def geometricFrobeniusExactIso :
    ExactFunctor.of (etaleModuleSheafPullback Λ (geometricFrobenius_ofFiniteField X)) ≅
      ExactFunctor.id (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) where
  hom := ⟨(geometricFrobeniusModuleIso X).hom⟩
  inv := ⟨(geometricFrobeniusModuleIso X).inv⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Derived restriction of `K` to the geometric fibre. -/
def geometricRestrictionDerived
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    DerivedCategory (Sheaf (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (etaleModuleSheafPullback Λ
      (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).mapDerivedCategory.obj K

/-- Unfolding of derived geometric restriction as `mapDerivedCategory` of module
sheaf pullback along `X_k̄ ⟶ X`. -/
theorem geometricRestrictionDerived_eq
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    geometricRestrictionDerived X K =
      (etaleModuleSheafPullback Λ
          (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).mapDerivedCategory.obj K :=
  sorry

/-- Two-step identification `((π_X)_{k̄})⁻¹(F|_{X_k̄}) ≅ F|_{X_k̄}` of sheaves of
left `Λ`-modules. -/
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
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
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
    DerivedCategory
      (Sheaf (FieldExtension.baseChange k (AlgebraicClosure k) X.hom).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (ModuleCat.{u + 1} Λ) :=
  etaleModuleDerivedGamma Λ (FieldExtension.baseChange k (AlgebraicClosure k) X.hom)

/-- Derived global sections `RΓ(X_k̄, K|_{X_k̄})`. -/
def geometricRGamma
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    DerivedCategory (ModuleCat.{u + 1} Λ) :=
  (geometricRGammaFunctor X).obj (geometricRestrictionDerived X K)

/-- Unfolding of `geometricRGamma` as derived sections of the geometric restriction. -/
theorem geometricRGamma_eq
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    geometricRGamma X K =
      (geometricRGammaFunctor X).obj (geometricRestrictionDerived X K) :=
  sorry

/-- Pullback of derived global sections along `(π_X)_{k̄}`. -/
def geometricRGammaPullback :
    geometricRGammaFunctor X ⟶
      (etaleModuleSheafPullback Λ (geometricFrobeniusBaseChange X)).mapDerivedCategory ⋙
        geometricRGammaFunctor X :=
  let fibre := FieldExtension.baseChange k (AlgebraicClosure k) X.hom
  (etaleModuleDerivedGamma Λ fibre).rightDerivedDesc
    (RightDerived.Cochain.unit (etaleModuleGamma Λ fibre))
    (HomologicalComplex.quasiIso
      (Sheaf fibre.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (up ℤ))
    ((etaleModuleSheafPullback Λ (geometricFrobeniusBaseChange X)).mapDerivedCategory ⋙
      etaleModuleDerivedGamma Λ fibre)
    (whiskerRight
        (NatTrans.mapHomologicalComplex
          (etaleModuleGammaPullback Λ (geometricFrobeniusBaseChange X)) (up ℤ))
        DerivedCategory.Q ≫
      RightDerived.Cochain.ExactFirst.unit
        (ExactFunctor.of (etaleModuleSheafPullback Λ (geometricFrobeniusBaseChange X)))
        (etaleModuleGamma Λ fibre))

/-- Geometric Frobenius pullback `π_X^*` on `RΓ(X_k̄, K|_{X_k̄})`. -/
def geometricFrobeniusRGamma
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    CategoryTheory.End (geometricRGamma X K) :=
  (geometricRGammaPullback X).app (geometricRestrictionDerived X K) ≫
    (geometricRGammaFunctor X).map (geometricFrobeniusRestrictionDerivedIso X K).hom

/-- Unfolding of `π_X^*` as derived sections-pullback along `(π_X)_{k̄}` followed
by the two-step coefficient identification. -/
theorem geometricFrobeniusRGamma_spec
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    geometricFrobeniusRGamma X K =
      (geometricRGammaPullback X).app (geometricRestrictionDerived X K) ≫
        (geometricRGammaFunctor X).map
          (geometricFrobeniusRestrictionDerivedIso X K).hom :=
  sorry

variable [ConnectedSpace X.left] [ConnectedSpace (Spec (CommRingCat.of k))]
variable [ConnectedSpace (geometricBaseChange X)]
variable (etaBar : GeometricPoint X.left)
variable [∀ U : X.left.Etale,
    HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]

/-- Package a finite discrete `π₁`-module as a finite-type object of the Galois
equivalence. -/
def toFiniteTypePi1Module
    (M : DiscreteModuleCat Λ (DegreeExtension.ofEtaleFundamentalGroup X etaBar).middle)
    (hM : Module.Finite Λ M.obj.V) :
    (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber etaBar))).FullSubcategory :=
  ⟨M, hM⟩

/-- The underlying discrete module of `toFiniteTypePi1Module` is the original module. -/
theorem toFiniteTypePi1Module_obj
    (M : DiscreteModuleCat Λ (DegreeExtension.ofEtaleFundamentalGroup X etaBar).middle)
    (hM : Module.Finite Λ M.obj.V) :
    (toFiniteTypePi1Module X etaBar M hM).obj = M :=
  sorry

/-- The derived object of `F_ρ` in `D(X_ét, Λ)`. -/
def pi1ModuleDerived [Finite Λ]
    (M : DiscreteModuleCat Λ (DegreeExtension.ofEtaleFundamentalGroup X etaBar).middle)
    (hM : Module.Finite Λ M.obj.V) :
    DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (DerivedCategory.singleFunctor
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (0 : ℤ)).obj
    (sheafOfPi1Module etaBar Λ (toFiniteTypePi1Module X etaBar M hM))

/-- Unfolding of `pi1ModuleDerived` as the degree-zero embedding of `sheafOfPi1Module`. -/
theorem pi1ModuleDerived_eq [Finite Λ]
    (M : DiscreteModuleCat Λ (DegreeExtension.ofEtaleFundamentalGroup X etaBar).middle)
    (hM : Module.Finite Λ M.obj.V) :
    pi1ModuleDerived X etaBar M hM =
      (DerivedCategory.singleFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (0 : ℤ)).obj
        (sheafOfPi1Module etaBar Λ (toFiniteTypePi1Module X etaBar M hM)) :=
  sorry

/-- On a projective curve, `RΓ(X_k̄, F_ρ)` is a perfect object of `D(Λ)`. -/
theorem isPerfect_geometricRGamma [Curve X] [Projective X.hom] [Finite Λ]
    (M : DiscreteModuleCat Λ (DegreeExtension.ofEtaleFundamentalGroup X etaBar).middle)
    (hM : Module.Finite Λ M.obj.V) :
    DerivedCategory.IsPerfect (geometricRGamma X (pi1ModuleDerived X etaBar M hM)) :=
  sorry

end AlgebraicGeometry.SchemeOverField
