module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import stacks_project.Chap59.Definition_59_77_1
public import stacks_project.Chap59.Lemma_59_71_5
public import stacks_project.Chap64.Proposition_64_13_1_GeometricSections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfectness of geometric derived global sections on a projective curve

This leaf records that `RΓ(X_k̄, K)` is a perfect object of `D(Λ)` when `X`
is a projective curve over a field `k` and `K` lies in `D_ctf(X, Λ)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.SchemeOverField
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory Opposite
open scoped AlgebraicGeometry MonoidalCategory Ring

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable {Λ : Type u} [CommRing Λ] [Finite Λ] [IsNoetherianRing Λ]
variable [HasColimitsOfSize.{u, u} (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
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

/-- Proposition 64.13.1. Let `X` be a projective curve over a field `k`, `Λ` a
finite ring, and `K` an object of `D_ctf(X, Λ)`. Then `RΓ(X_k̄, K)` is a
perfect object of `D(Λ)`.

Here `D_ctf` is `EtaleConstructibleTorFinite` with constructible étale module
sheaves and `DerivedTensor.HasFiniteTorDimension`, `X_k̄` is `geometricFibre X`,
`RΓ(X_k̄, K|_{X_k̄})` is `rGammaGeometricFibre`, and `D_perf(Λ)` is
`DerivedCategory.IsPerfect`. Perfectness is the characterization of
Lemma 64.12.2: finite cohomology modules together with finite Tor-dimension. -/
@[stacks 03TV]
theorem isPerfect_rGammaGeometricFibre (X : SchemeOverField k)
    [Curve X] [Projective X.hom]
    (K : Scheme.EtaleConstructibleTorFinite X.left Λ
      (fun F ↦ Sheaf.IsConstructibleEtaleModule
        (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
        (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
      DerivedTensor.HasFiniteTorDimension) :
    DerivedCategory.IsPerfect (rGammaGeometricFibre X K.obj.obj) :=
  sorry

/-- Each cohomology module of `RΓ(X_k̄, K)` is a finite `Λ`-module. -/
theorem rGammaGeometricFibre_homology_finite (X : SchemeOverField k)
    [Curve X] [Projective X.hom]
    (K : Scheme.EtaleConstructibleTorFinite X.left Λ
      (fun F ↦ Sheaf.IsConstructibleEtaleModule
        (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
        (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
      DerivedTensor.HasFiniteTorDimension) :
    ∀ i : ℤ, Module.Finite Λ
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Λ) i).obj
        (rGammaGeometricFibre X K.obj.obj)) :=
  sorry

/-- `RΓ(X_k̄, K)` has finite Tor-dimension over `Λ`. -/
theorem rGammaGeometricFibre_hasFiniteTorDimension (X : SchemeOverField k)
    [Curve X] [Projective X.hom]
    (K : Scheme.EtaleConstructibleTorFinite X.left Λ
      (fun F ↦ Sheaf.IsConstructibleEtaleModule
        (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
        (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
      DerivedTensor.HasFiniteTorDimension) :
    HasFiniteTorDimension Λ (rGammaGeometricFibre X K.obj.obj) :=
  sorry

variable [Fintype k] {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]

/-- On a finite field, field-general geometric derived sections agree with the
Frobenius-ready owner `geometricRGamma`. -/
theorem rGammaGeometricFibre_eq_geometricRGamma (X : SchemeOverField k)
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    rGammaGeometricFibre X K = geometricRGamma X K :=
  sorry

end AlgebraicGeometry.SchemeOverField
