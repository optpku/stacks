/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import stacks_project.Chap59.Definition_59_77_1
public import stacks_project.Chap59.Lemma_59_71_5
public import stacks_project.Chap64.«64_16_1_1_CompactSupport»

/-!
# Lefschetz trace formula for constructible complexes of finite Tor-dimension
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.SchemeOverField.CompactSupportTrace
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory Opposite ComplexShape
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
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension F]
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

/-- Theorem 64.20.4 (1). For a finite-type scheme `X` over a finite field `k`,
a finite ring `Λ` with `#Λ` invertible in `k`, and `K` in `D_ctf(X, Λ)`, the
compactly supported geometric derived sections `RΓ_c(X_k̄, K)` given by
`geometricRGammaCompactSupport` are a perfect object of `D(Λ)`. Here `D_ctf`
is `EtaleConstructibleTorFinite` and `D_perf` is `DerivedCategory.IsPerfect`. -/
@[stacks 03V3]
theorem isPerfect_geometricRGammaCompactSupport_of_constructibleTorFinite
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
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
    (hΛ : Nat.Coprime (Nat.card Λ) p)
    (K : Scheme.EtaleConstructibleTorFinite X.left Λ
      (fun F ↦ Sheaf.IsConstructibleEtaleModule
        (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
        (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
      DerivedTensor.HasFiniteTorDimension) :
    DerivedCategory.IsPerfect (geometricRGammaCompactSupport X P K.obj.obj) :=
  sorry

/-- Theorem 64.20.4 (2). In the same setup as Theorem 64.20.4 (1), the sum of
traces of geometric Frobenius `π_x` (`geometricFrobeniusDerivedStalk`) on the
derived geometric stalks `K_x̄` at `k`-points `X(k)` (morphisms `𝟙_ ⟶ X`)
equals the trace of `π_X^*` (`geometricFrobeniusRGammaCompactSupport`) on
`RΓ_c(X_k̄, K)` (`geometricRGammaCompactSupport`), as an equality in `Λ♮`. -/
@[stacks 03V3]
theorem lefschetzTraceFormula_of_constructibleTorFinite
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
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
    (hΛ : Nat.Coprime (Nat.card Λ) p)
    (K : Scheme.EtaleConstructibleTorFinite X.left Λ
      (fun F ↦ Sheaf.IsConstructibleEtaleModule
        (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
        (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
      DerivedTensor.HasFiniteTorDimension) :
    traceGeometricFrobeniusCompactSupport X P K.obj.obj
        (isPerfect_geometricRGammaCompactSupport_of_constructibleTorFinite X P hΛ K) =
      traceGeometricFrobeniusStalks K.obj.obj
        (fun x ↦ isPerfect_geometricDerivedStalk K x) :=
  sorry

end AlgebraicGeometry.SchemeOverField
