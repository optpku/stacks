/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.FixedInterior
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain.ExactFirst
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import stacks_project.Chap59.«59_56_0_1»
public import stacks_project.Chap59.Definition_59_70_1_ExtensionByZero
public import stacks_project.Chap59.Definition_59_77_1
public import stacks_project.Chap59.Lemma_59_39_1
public import stacks_project.Chap59.Lemma_59_71_5
public import stacks_project.Chap63.Definition_63_12_1_Gamma
public import stacks_project.Chap64.«64_2_0_1_GeometricFrobenius»
public import stacks_project.Chap64.Proposition_64_10_2_Trace
public import stacks_project.Chap64.Theorem_64_3_9_Pullback

/-!
# Compactly supported geometric derived sections

This leaf owns `RΓ_c(X_k̄, K) := RΓ(X̄_k̄, j_! K)` for a compactification
`j : X ↪ X̄`, the induced geometric-Frobenius endomorphism `π_X^*`, and the
compact-support and stalk-side traces in `Λ♮`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
open GrothendieckTopology.Point Opposite ComplexShape
open scoped AlgebraicGeometry MonoidalCategory Ring

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {Λ : Type u} [CommRing Λ] [Finite Λ] [IsNoetherianRing Λ]
variable [HasColimitsOfSize.{u, u} (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}},
    HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ {Y : Scheme.{u}},
    ((sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
      (op (Etale.globalEtale Y))).Additive]
variable [∀ {Y : Scheme.{u}},
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
          (op (Etale.globalEtale Y))))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (up ℤ))]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

/-- Inverse image of sheaves of `Λ`-modules along a morphism of schemes. -/
abbrev etaleModuleSheafPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ) :=
  (smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
    Y.smallEtaleTopology X.smallEtaleTopology

variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
      Y.smallEtaleTopology X.smallEtaleTopology).Additive]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    PreservesFiniteLimits
      ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
        Y.smallEtaleTopology X.smallEtaleTopology)]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    PreservesFiniteColimits
      ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
        Y.smallEtaleTopology X.smallEtaleTopology)]
variable [∀ {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B),
    (((smallEtalePullback p).sheafPullback (ModuleCat.{u} Λ)
        A.smallEtaleTopology B.smallEtaleTopology) ⋙
      ((smallEtalePullback q).sheafPullback (ModuleCat.{u} Λ)
        B.smallEtaleTopology C.smallEtaleTopology)).Additive]
variable [∀ {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B),
    PreservesFiniteLimits
      (((smallEtalePullback p).sheafPullback (ModuleCat.{u} Λ)
          A.smallEtaleTopology B.smallEtaleTopology) ⋙
        ((smallEtalePullback q).sheafPullback (ModuleCat.{u} Λ)
          B.smallEtaleTopology C.smallEtaleTopology))]
variable [∀ {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B),
    PreservesFiniteColimits
      (((smallEtalePullback p).sheafPullback (ModuleCat.{u} Λ)
          A.smallEtaleTopology B.smallEtaleTopology) ⋙
        ((smallEtalePullback q).sheafPullback (ModuleCat.{u} Λ)
          B.smallEtaleTopology C.smallEtaleTopology))]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).Additive]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    PreservesFiniteLimits (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ))]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    PreservesFiniteColimits (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ))]
variable [∀ {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B),
    (Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ) ⋙
      Sheaf.smallEtaleInverseImage q (ModuleCat.{u} Λ)).Additive]
variable [∀ {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B),
    PreservesFiniteLimits
      (Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ) ⋙
        Sheaf.smallEtaleInverseImage q (ModuleCat.{u} Λ))]
variable [∀ {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B),
    PreservesFiniteColimits
      (Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ) ⋙
        Sheaf.smallEtaleInverseImage q (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}},
    MonoidalCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}},
    MonoidalPreadditive (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}}
    (K L : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
      (ComplexShape.up ℤ)]
variable [∀ {Y : Scheme.{u}},
    DerivedTensor.Right.Has
      (C := Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Inverse-image identification along equal morphisms. -/
def etaleModuleSheafPullback_congr {A B : Scheme.{u}} {p q : A ⟶ B} (h : p = q)
    [∀ F : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback p).op.HasLeftKanExtension F]
    [∀ F : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback q).op.HasLeftKanExtension F] :
    (smallEtalePullback p).sheafPullback (ModuleCat.{u} Λ)
        B.smallEtaleTopology A.smallEtaleTopology ≅
      (smallEtalePullback q).sheafPullback (ModuleCat.{u} Λ)
        B.smallEtaleTopology A.smallEtaleTopology :=
  h ▸ Iso.refl _

/-- Pullback of module sheaves along a composite is the composite pullback. -/
def etaleModuleSheafPullback_comp {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B)
    [∀ F : A.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback p).op.HasLeftKanExtension F]
    [∀ F : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback q).op.HasLeftKanExtension F]
    [∀ F : A.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (q ≫ p)).op.HasLeftKanExtension F] :
    (smallEtalePullback p).sheafPullback (ModuleCat.{u} Λ)
          A.smallEtaleTopology B.smallEtaleTopology ⋙
        (smallEtalePullback q).sheafPullback (ModuleCat.{u} Λ)
          B.smallEtaleTopology C.smallEtaleTopology ≅
      (smallEtalePullback (q ≫ p)).sheafPullback (ModuleCat.{u} Λ)
        A.smallEtaleTopology C.smallEtaleTopology :=
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

/-- Canonical identification `π_X⁻¹ F ≅ F` of sheaves of `Λ`-modules, induced by
the small-étale site isomorphism of geometric Frobenius. -/
def geometricFrobeniusSheafIso_module (X : SchemeOverField k) :
    (smallEtalePullback (geometricFrobenius_ofFiniteField X)).sheafPullback
        (ModuleCat.{u} Λ) X.left.smallEtaleTopology X.left.smallEtaleTopology ≅
      𝟭 (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  Adjunction.leftAdjointUniq
    ((smallEtalePullback (geometricFrobenius_ofFiniteField X)).sheafAdjunctionContinuous
      (ModuleCat.{u} Λ) X.left.smallEtaleTopology X.left.smallEtaleTopology)
    (Adjunction.id.ofNatIsoRight
      (sheafPushforwardContinuousId'
        (geometricFrobenius_smallEtalePullbackIso X).symm (ModuleCat.{u} Λ)
        X.left.smallEtaleTopology).symm)

/-- Two-step identification `((π_X)_{k̄})⁻¹(F|_{X_k̄}) ≅ F|_{X_k̄}` of sheaves of
`Λ`-modules. -/
def compactSupportFrobeniusModuleRestrictionIso (X : SchemeOverField k) :
    (smallEtalePullback
            (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).sheafPullback
          (ModuleCat.{u} Λ) X.left.smallEtaleTopology
          (FieldExtension.baseChange k (AlgebraicClosure k) X.hom).smallEtaleTopology ⋙
        (smallEtalePullback (geometricFrobeniusBaseChange X)).sheafPullback
          (ModuleCat.{u} Λ)
          (FieldExtension.baseChange k (AlgebraicClosure k) X.hom).smallEtaleTopology
          (FieldExtension.baseChange k (AlgebraicClosure k) X.hom).smallEtaleTopology ≅
      (smallEtalePullback
          (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).sheafPullback
        (ModuleCat.{u} Λ) X.left.smallEtaleTopology
        (FieldExtension.baseChange k (AlgebraicClosure k) X.hom).smallEtaleTopology :=
  etaleModuleSheafPullback_comp
      (FieldExtension.toSource k (AlgebraicClosure k) X.hom)
      (geometricFrobeniusBaseChange X) ≪≫
    etaleModuleSheafPullback_congr (geometricFrobeniusBaseChange_comp_toSource X) ≪≫
      (etaleModuleSheafPullback_comp (geometricFrobenius_ofFiniteField X)
          (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).symm ≪≫
        isoWhiskerRight (geometricFrobeniusSheafIso_module X)
            (etaleModuleSheafPullback
              (FieldExtension.toSource k (AlgebraicClosure k) X.hom)) ≪≫
          leftUnitor _

/-- Bundled exact-functor isomorphism underlying
`compactSupportFrobeniusModuleRestrictionIso`. -/
def compactSupportFrobeniusRestrictionExactIso (X : SchemeOverField k) :
    ExactFunctor.of
        ((smallEtalePullback
              (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).sheafPullback
            (ModuleCat.{u} Λ) X.left.smallEtaleTopology
            (FieldExtension.baseChange k (AlgebraicClosure k) X.hom).smallEtaleTopology ⋙
          (smallEtalePullback (geometricFrobeniusBaseChange X)).sheafPullback
            (ModuleCat.{u} Λ)
            (FieldExtension.baseChange k (AlgebraicClosure k) X.hom).smallEtaleTopology
            (FieldExtension.baseChange k (AlgebraicClosure k) X.hom).smallEtaleTopology) ≅
      ExactFunctor.of
        ((smallEtalePullback
            (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).sheafPullback
          (ModuleCat.{u} Λ) X.left.smallEtaleTopology
          (FieldExtension.baseChange k (AlgebraicClosure k) X.hom).smallEtaleTopology) where
  hom := ⟨(compactSupportFrobeniusModuleRestrictionIso X).hom⟩
  inv := ⟨(compactSupportFrobeniusModuleRestrictionIso X).inv⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Pullback of underived global sections along inverse image of module sheaves. -/
def etaleModuleSectionsPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
        (op (Etale.globalEtale Y)) ⟶
      etaleModuleSheafPullback f ⋙
        (sheafSections X.smallEtaleTopology (ModuleCat.{u} Λ)).obj
          (op (Etale.globalEtale X)) where
  app F :=
    ((sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)).map
        (((smallEtalePullback f).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
            Y.smallEtaleTopology X.smallEtaleTopology).unit.app F)).app
      (op (Etale.globalEtale Y)) ≫
      ((etaleModuleSheafPullback f).obj F).obj.map
        (op (Etale.globalEtalePullbackIso f).inv)
  naturality := fun _ _ _ ↦ sorry

/-- Extension by zero `j_! K` of an étale derived `Λ`-module complex along the
interior immersion of a compactification. -/
def geometricExtensionByZero (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    [Etale (Compactification.Of.ι P)]
    [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
    [(etaleExtensionByZero (Compactification.Of.ι P)
        (ModuleCat.{u} Λ)).Additive]
    [PreservesFiniteLimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    [PreservesFiniteColimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    (K : EtaleDerived X.left Λ) :
    EtaleDerived P.obj.right.left Λ :=
  (etaleExtensionByZero (Compactification.Of.ι P)
      (ModuleCat.{u} Λ)).mapDerivedCategory.obj K

/-- Unfolding of `geometricExtensionByZero` as `mapDerivedCategory` of étale
extension by zero along `Compactification.Of.ι P`. -/
theorem geometricExtensionByZero_eq (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    [Etale (Compactification.Of.ι P)]
    [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
    [(etaleExtensionByZero (Compactification.Of.ι P)
        (ModuleCat.{u} Λ)).Additive]
    [PreservesFiniteLimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    [PreservesFiniteColimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    (K : EtaleDerived X.left Λ) :
    geometricExtensionByZero X P K =
      (etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} Λ)).mapDerivedCategory.obj K :=
  sorry

/-- Restriction of `j_! K` to the geometric fibre of the compactification. -/
def geometricRestrictionCompactSupport (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    [Etale (Compactification.Of.ι P)]
    [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
    [(etaleExtensionByZero (Compactification.Of.ι P)
        (ModuleCat.{u} Λ)).Additive]
    [PreservesFiniteLimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    [PreservesFiniteColimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    (K : EtaleDerived X.left Λ) :
    EtaleDerived
      (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom) Λ :=
  (etaleModuleSheafPullback
      (FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom)).mapDerivedCategory.obj
    (geometricExtensionByZero X P K)

/-- Unfolding of geometric restriction of extension by zero as inverse image
along `X̄_k̄ ⟶ X̄`. -/
theorem geometricRestrictionCompactSupport_eq (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    [Etale (Compactification.Of.ι P)]
    [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
    [(etaleExtensionByZero (Compactification.Of.ι P)
        (ModuleCat.{u} Λ)).Additive]
    [PreservesFiniteLimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    [PreservesFiniteColimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    (K : EtaleDerived X.left Λ) :
    geometricRestrictionCompactSupport X P K =
      (etaleModuleSheafPullback
          (FieldExtension.toSource k (AlgebraicClosure k)
            P.obj.right.hom)).mapDerivedCategory.obj
        (geometricExtensionByZero X P K) :=
  sorry

/-- Compactly supported derived sections `RΓ_c(X_k̄, K)`, defined as
`RΓ(X̄_k̄, j_! K)` for a compactification `j : X ↪ X̄`. -/
def geometricRGammaCompactSupport (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    [Etale (Compactification.Of.ι P)]
    [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
    [(etaleExtensionByZero (Compactification.Of.ι P)
        (ModuleCat.{u} Λ)).Additive]
    [PreservesFiniteLimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    [PreservesFiniteColimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    (K : EtaleDerived X.left Λ) :
    DerivedCategory (ModuleCat.{u} Λ) :=
  (etaleDerivedGamma
      (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom) Λ).obj
    (geometricRestrictionCompactSupport X P K)

/-- Unfolding of compactly supported derived sections as `RΓ` of the geometric
fibre of the compactification, applied to `j_! K`. -/
theorem geometricRGammaCompactSupport_eq (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    [Etale (Compactification.Of.ι P)]
    [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
    [(etaleExtensionByZero (Compactification.Of.ι P)
        (ModuleCat.{u} Λ)).Additive]
    [PreservesFiniteLimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    [PreservesFiniteColimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    (K : EtaleDerived X.left Λ) :
    geometricRGammaCompactSupport X P K =
      (etaleDerivedGamma
          (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom)
          Λ).obj
        (geometricRestrictionCompactSupport X P K) :=
  sorry

/-- Derived two-step identification
`((π_{X̄})_{k̄})⁻¹((j_! K)|_{X̄_k̄}) ≅ (j_! K)|_{X̄_k̄}`. -/
def geometricFrobeniusRestrictionCompactSupportIso (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    [Etale (Compactification.Of.ι P)]
    [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
    [(etaleExtensionByZero (Compactification.Of.ι P)
        (ModuleCat.{u} Λ)).Additive]
    [PreservesFiniteLimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    [PreservesFiniteColimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    (K : EtaleDerived X.left Λ) :
    (etaleModuleSheafPullback
        (geometricFrobeniusBaseChange P.obj.right)).mapDerivedCategory.obj
        (geometricRestrictionCompactSupport X P K) ≅
      geometricRestrictionCompactSupport X P K :=
  ((ExactFunctor.MapDerivedCategory.compFunctorIso
          (ExactFunctor.of
            (etaleModuleSheafPullback
              (FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom)))
          (ExactFunctor.of
            (etaleModuleSheafPullback
              (geometricFrobeniusBaseChange P.obj.right)))).symm ≪≫
      ExactFunctor.MapDerivedCategory.mapIso
        (compactSupportFrobeniusRestrictionExactIso P.obj.right)).app
    (geometricExtensionByZero X P K)

/-- `RΓ` on the small-étale site is a right derived functor of cochain-level
sections at the identity étale object. -/
instance instIsRightDerivedFunctor_etaleDerivedGamma (Y : Scheme.{u}) :
    (etaleDerivedGamma Y Λ).IsRightDerivedFunctor
      (RightDerived.Cochain.unit
        ((sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
          (op (Etale.globalEtale Y))))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (up ℤ)) :=
  sorry

/-- Pullback of derived global sections along `(π_{X̄})_{k̄}`. -/
def geometricRGammaCompactSupportPullback (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X) :
    etaleDerivedGamma
        (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom) Λ ⟶
      (etaleModuleSheafPullback
          (geometricFrobeniusBaseChange P.obj.right)).mapDerivedCategory ⋙
        etaleDerivedGamma
          (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom) Λ :=
  (etaleDerivedGamma
        (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom)
        Λ).rightDerivedDesc
    (RightDerived.Cochain.unit
      ((sheafSections
          (FieldExtension.baseChange k (AlgebraicClosure k)
            P.obj.right.hom).smallEtaleTopology
          (ModuleCat.{u} Λ)).obj
        (op (Etale.globalEtale
          (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom)))))
    (HomologicalComplex.quasiIso
      (Sheaf
        (FieldExtension.baseChange k (AlgebraicClosure k)
          P.obj.right.hom).smallEtaleTopology
        (ModuleCat.{u} Λ))
      (up ℤ))
    ((etaleModuleSheafPullback
          (geometricFrobeniusBaseChange P.obj.right)).mapDerivedCategory ⋙
      etaleDerivedGamma
        (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom) Λ)
    (whiskerRight
        (NatTrans.mapHomologicalComplex
          (etaleModuleSectionsPullback (geometricFrobeniusBaseChange P.obj.right))
          (up ℤ))
        (DerivedCategory.Q :
          CochainComplex (ModuleCat.{u} Λ) ℤ ⥤ DerivedCategory (ModuleCat.{u} Λ)) ≫
      RightDerived.Cochain.ExactFirst.unit
        (ExactFunctor.of
          (etaleModuleSheafPullback (geometricFrobeniusBaseChange P.obj.right)))
        ((sheafSections
            (FieldExtension.baseChange k (AlgebraicClosure k)
              P.obj.right.hom).smallEtaleTopology
            (ModuleCat.{u} Λ)).obj
          (op (Etale.globalEtale
            (FieldExtension.baseChange k (AlgebraicClosure k)
              P.obj.right.hom)))))

/-- Geometric Frobenius pullback `π_X^*` on `RΓ_c(X_k̄, K)`. -/
def geometricFrobeniusRGammaCompactSupport (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    [Etale (Compactification.Of.ι P)]
    [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
    [(etaleExtensionByZero (Compactification.Of.ι P)
        (ModuleCat.{u} Λ)).Additive]
    [PreservesFiniteLimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    [PreservesFiniteColimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    (K : EtaleDerived X.left Λ) :
    End (geometricRGammaCompactSupport X P K) :=
  (geometricRGammaCompactSupportPullback X P).app
      (geometricRestrictionCompactSupport X P K) ≫
    (etaleDerivedGamma
        (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom)
        Λ).map
      (geometricFrobeniusRestrictionCompactSupportIso X P K).hom

/-- Unfolding of compact-support geometric Frobenius as sections-pullback along
`(π_{X̄})_{k̄}` followed by the two-step coefficient identification. -/
theorem geometricFrobeniusRGammaCompactSupport_spec (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    [Etale (Compactification.Of.ι P)]
    [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
    [(etaleExtensionByZero (Compactification.Of.ι P)
        (ModuleCat.{u} Λ)).Additive]
    [PreservesFiniteLimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    [PreservesFiniteColimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    (K : EtaleDerived X.left Λ) :
    geometricFrobeniusRGammaCompactSupport X P K =
      (geometricRGammaCompactSupportPullback X P).app
          (geometricRestrictionCompactSupport X P K) ≫
        (etaleDerivedGamma
            (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom)
            Λ).map
          (geometricFrobeniusRestrictionCompactSupportIso X P K).hom :=
  sorry

/-- On a finite-type scheme of dimension at most `1` with a projective
compactification, `RΓ_c(X_k̄, K)` is a perfect object of `D(Λ)` for
`K` in `D_ctf(X, Λ)`. -/
theorem isPerfect_geometricRGammaCompactSupport (X : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom]
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    [Etale (Compactification.Of.ι P)]
    [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
    [(etaleExtensionByZero (Compactification.Of.ι P)
        (ModuleCat.{u} Λ)).Additive]
    [PreservesFiniteLimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    [PreservesFiniteColimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    [Projective P.obj.right.hom]
    (hdim : topologicalKrullDim X.left ≤ 1)
    (K : Scheme.EtaleConstructibleTorFinite X.left Λ
      (fun F ↦ Sheaf.IsConstructibleEtaleModule
        (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
        (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
      DerivedTensor.HasFiniteTorDimension) :
    DerivedCategory.IsPerfect (geometricRGammaCompactSupport X P K.obj.obj) :=
  sorry

/-- Trace `Tr(π_X^* | RΓ_c(X_k̄, K))` in `Λ♮`. -/
def traceGeometricFrobeniusCompactSupport (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    [Etale (Compactification.Of.ι P)]
    [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
    [(etaleExtensionByZero (Compactification.Of.ι P)
        (ModuleCat.{u} Λ)).Additive]
    [PreservesFiniteLimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    [PreservesFiniteColimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    (K : EtaleDerived X.left Λ)
    (hK : DerivedCategory.IsPerfect (geometricRGammaCompactSupport X P K)) :
    Λ♮ :=
  hK.traceNatural (geometricFrobeniusRGammaCompactSupport X P K)

/-- The compact-support Frobenius trace is the finite-projective trace of
`π_X^*`. -/
theorem traceGeometricFrobeniusCompactSupport_spec (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    [Etale (Compactification.Of.ι P)]
    [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
    [(etaleExtensionByZero (Compactification.Of.ι P)
        (ModuleCat.{u} Λ)).Additive]
    [PreservesFiniteLimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    [PreservesFiniteColimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    (K : EtaleDerived X.left Λ)
    (hK : DerivedCategory.IsPerfect (geometricRGammaCompactSupport X P K)) :
    traceGeometricFrobeniusCompactSupport X P K hK =
      hK.traceNatural (geometricFrobeniusRGammaCompactSupport X P K) :=
  sorry

/-- The compact-support Frobenius trace is independent of the choice of
projective compactification. -/
theorem traceGeometricFrobeniusCompactSupport_independent
    (X : SchemeOverField k)
    (P Q : Compactification.Of (Spec (CommRingCat.of k)) X)
    [Etale (Compactification.Of.ι P)] [Etale (Compactification.Of.ι Q)]
    [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
    [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction (Compactification.Of.ι Q)).op.HasLeftKanExtension F]
    [(etaleExtensionByZero (Compactification.Of.ι P)
        (ModuleCat.{u} Λ)).Additive]
    [(etaleExtensionByZero (Compactification.Of.ι Q)
        (ModuleCat.{u} Λ)).Additive]
    [PreservesFiniteLimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    [PreservesFiniteLimits
        (etaleExtensionByZero (Compactification.Of.ι Q) (ModuleCat.{u} Λ))]
    [PreservesFiniteColimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    [PreservesFiniteColimits
        (etaleExtensionByZero (Compactification.Of.ι Q) (ModuleCat.{u} Λ))]
    [Projective P.obj.right.hom] [Projective Q.obj.right.hom]
    (K : EtaleDerived X.left Λ)
    (hP : DerivedCategory.IsPerfect (geometricRGammaCompactSupport X P K))
    (hQ : DerivedCategory.IsPerfect (geometricRGammaCompactSupport X Q K)) :
    traceGeometricFrobeniusCompactSupport X P K hP =
      traceGeometricFrobeniusCompactSupport X Q K hQ :=
  sorry

namespace CompactSupportTrace

/-- Small-étale stalk functor of sheaves of `Λ`-modules at the geometric point
of a `k`-rational point. -/
def geometricStalkFunctor {X : SchemeOverField k}
    (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ) ⥤ ModuleCat.{u} Λ :=
  ((Scheme.pointSmallEtale (homSpecGeometric x)).sheafFiber :
      Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ) ⥤ ModuleCat.{u} Λ)

/-- Small-étale module stalks at a rational geometric point are additive. -/
instance instAdditive_geometricStalkFunctor {X : SchemeOverField k}
    (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    @Functor.Additive
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ModuleCat.{u} Λ) _ _
      Abelian.toPreadditive ModuleCat.abelian.toPreadditive
      (geometricStalkFunctor x) :=
  sorry

/-- Small-étale module stalks at a rational geometric point preserve finite
limits. -/
instance instPreservesFiniteLimits_geometricStalkFunctor {X : SchemeOverField k}
    (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    PreservesFiniteLimits
      (geometricStalkFunctor x :
        Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ) ⥤ ModuleCat.{u} Λ) :=
  sorry

/-- Small-étale module stalks at a rational geometric point preserve finite
colimits. -/
instance instPreservesFiniteColimits_geometricStalkFunctor
    {X : SchemeOverField k} (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    PreservesFiniteColimits
      (geometricStalkFunctor x :
        Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ) ⥤ ModuleCat.{u} Λ) :=
  sorry

/-- Derived geometric stalk `K_x̄` of an étale `Λ`-module complex at the
geometric point lying over a `k`-rational point. -/
def geometricDerivedStalk {X : SchemeOverField k} (K : EtaleDerived X.left Λ)
    (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    DerivedCategory (ModuleCat.{u} Λ) :=
  (geometricStalkFunctor x).mapDerivedCategory.obj K

/-- Unfolding of `geometricDerivedStalk` as `mapDerivedCategory` of the
small-étale module stalk functor. -/
theorem geometricDerivedStalk_spec {X : SchemeOverField k}
    (K : EtaleDerived X.left Λ) (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    geometricDerivedStalk K x =
      (geometricStalkFunctor x).mapDerivedCategory.obj K :=
  sorry

/-- Geometric Frobenius `π_x` on the derived geometric stalk `K_x̄`, as the
Galois action of the inverse of arithmetic Frobenius. -/
def geometricFrobeniusDerivedStalk {X : SchemeOverField k}
    (K : EtaleDerived X.left Λ) (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    End (geometricDerivedStalk K x) :=
  let τ : geometricStalkFunctor x ⟶ geometricStalkFunctor x :=
    Hom.sheafFiber
      ⟨geometricPointFiberMap (homSpecGeometric x)
        (geometricPointGaloisIso x arithmeticFrobeniusEquiv⁻¹)⟩
  (ExactFunctor.MapDerivedCategory.map
      (⟨τ⟩ : ExactFunctor.of (geometricStalkFunctor x) ⟶
        ExactFunctor.of (geometricStalkFunctor x))).app K

/-- Evaluating geometric Frobenius on a derived geometric stalk recovers the
derived Galois action of the inverse of arithmetic Frobenius. -/
theorem geometricFrobeniusDerivedStalk_spec {X : SchemeOverField k}
    (K : EtaleDerived X.left Λ) (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    geometricFrobeniusDerivedStalk K x =
      (ExactFunctor.MapDerivedCategory.map
          (⟨Hom.sheafFiber
              ⟨geometricPointFiberMap (homSpecGeometric x)
                (geometricPointGaloisIso x arithmeticFrobeniusEquiv⁻¹)⟩⟩ :
            ExactFunctor.of (geometricStalkFunctor x) ⟶
              ExactFunctor.of (geometricStalkFunctor x))).app K :=
  sorry

/-- Stalks of objects of `D_ctf(X, Λ)` at geometric points of rational points
are perfect objects of `D(Λ)`. -/
theorem isPerfect_geometricDerivedStalk {X : SchemeOverField k}
    (K : Scheme.EtaleConstructibleTorFinite X.left Λ
      (fun F ↦ Sheaf.IsConstructibleEtaleModule
        (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
        (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
      DerivedTensor.HasFiniteTorDimension)
    (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    DerivedCategory.IsPerfect (geometricDerivedStalk K.obj.obj x) :=
  sorry

/-- Local Lefschetz trace sum `∑_{x ∈ X(k)} Tr(π_x | K_x̄)` in `Λ♮`. -/
def traceGeometricFrobeniusStalks {X : SchemeOverField k}
    (K : EtaleDerived X.left Λ)
    (hK : ∀ x : (𝟙_ (SchemeOverField k) ⟶ X),
      DerivedCategory.IsPerfect (geometricDerivedStalk K x)) : Λ♮ :=
  ∑ᶠ x : (𝟙_ (SchemeOverField k) ⟶ X),
    (hK x).traceNatural (geometricFrobeniusDerivedStalk K x)

/-- Unfolding of the stalk-side trace as a finitely supported sum of traces of
geometric Frobenius on derived geometric stalks. -/
theorem traceGeometricFrobeniusStalks_spec {X : SchemeOverField k}
    (K : EtaleDerived X.left Λ)
    (hK : ∀ x : (𝟙_ (SchemeOverField k) ⟶ X),
      DerivedCategory.IsPerfect (geometricDerivedStalk K x)) :
    traceGeometricFrobeniusStalks K hK =
      ∑ᶠ x : (𝟙_ (SchemeOverField k) ⟶ X),
        (hK x).traceNatural (geometricFrobeniusDerivedStalk K x) :=
  sorry

end CompactSupportTrace

end AlgebraicGeometry.SchemeOverField
