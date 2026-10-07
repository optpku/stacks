module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import stacks_project.Chap59.Lemma_59_71_5
public import stacks_project.Chap64.Proposition_64_10_2_Trace
public import stacks_project.Chap64.«64_14_3_1_DerivedSections»
public import stacks_project.Chap64.«64_14_3_1_Stalk»
public import stacks_project.Chap64.«64_14_3_1_Trace»

/-!
# Lefschetz trace formula for constructible complexes of finite Tor dimension
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.SchemeOverField
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory Opposite
open scoped AlgebraicGeometry MonoidalCategory Ring

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {Λ : Type u} [CommRing Λ] [Finite Λ] [IsNoetherianRing Λ]
variable [HasColimitsOfSize.{u, u} (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}},
    CategoryWithHomology (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}},
    HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension P]
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
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
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

/-- Finite Tor-dimension of an object of `EtaleDerived Y Λ`. -/
abbrev etaleModuleFiniteTorDimension {Y : Scheme.{u}}
    (K : EtaleDerived Y Λ) : Prop :=
  DerivedTensor.HasFiniteTorDimension K

/-- Unfolding of finite Tor-dimension on étale derived modules. -/
theorem etaleModuleFiniteTorDimension_eq {Y : Scheme.{u}}
    (K : EtaleDerived Y Λ) :
    etaleModuleFiniteTorDimension K = DerivedTensor.HasFiniteTorDimension K :=
  sorry

/-- Constructibility of a small-étale sheaf of left `Λ`-modules, via inverse
image along `smallEtaleInverseImage` and finite-type local constancy. -/
abbrev etaleModuleConstructible {Y : Scheme.{u}}
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) : Prop :=
  Sheaf.IsConstructibleEtaleModule
    (fun {Z} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
    (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F

/-- Unfolding of constructibility for étale sheaves of left `Λ`-modules. -/
theorem etaleModuleConstructible_eq {Y : Scheme.{u}}
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    etaleModuleConstructible F =
      Sheaf.IsConstructibleEtaleModule
        (fun {Z} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
        (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F :=
  sorry

variable (Λ) in
/-- The derived category `D_ctf(X_etale, Λ)` of constructible complexes of
finite Tor dimension, with restriction along small-étale inverse image and
finite-type local constancy. -/
abbrev etaleConstructibleTorFinite (X : Scheme.{u}) :=
  Scheme.EtaleConstructibleTorFinite X Λ
    etaleModuleConstructible etaleModuleFiniteTorDimension

variable (Λ) in
/-- Unfolding of `etaleConstructibleTorFinite` as the constructible finite-Tor
full subcategory of `EtaleDerived`. -/
theorem etaleConstructibleTorFinite_eq (X : Scheme.{u}) :
    etaleConstructibleTorFinite Λ X =
      Scheme.EtaleConstructibleTorFinite X Λ
        etaleModuleConstructible etaleModuleFiniteTorDimension :=
  sorry

/-- 64.14.3.1: Lefschetz trace formula. For a projective curve `X` over a
finite field `k`, a finite ring `Λ`, and `K` in `D_ctf(X, Λ)`,
`Tr(π_X^* | RΓ(X_k̄, K))` equals `∑_{x ∈ X(k)} Tr(π_X | K_x̄)` in `Λ♮`.
Here `X(k)` is identified with morphisms `𝟙_ ⟶ X`, `π_X^*` is
`geometricFrobeniusRGamma`, `RΓ` is `geometricRGamma`, and `π_X` on stalks is
`geometricFrobeniusDerivedStalk`. -/
@[stacks 03U0]
theorem lefschetzTraceFormula (X : SchemeOverField k) [Curve X] [Projective X.hom]
    (K : etaleConstructibleTorFinite Λ X.left) :
    (isPerfect_geometricRGamma X K).traceNatural
        (geometricFrobeniusRGamma X K.obj.obj) =
      traceGeometricFrobeniusStalks X K.obj.obj
        (fun x ↦ isPerfect_geometricDerivedStalk K x) :=
  sorry

end AlgebraicGeometry.SchemeOverField
