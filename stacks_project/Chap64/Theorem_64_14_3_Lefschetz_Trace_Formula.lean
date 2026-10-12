/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap64.Definition_64_14_1
public import stacks_project.Chap64.«64_14_3_1»

/-!
# Lefschetz trace formula

The named equality of the global Lefschetz number with the local stalk-sum
trace, for constructible complexes of finite Tor-dimension on a projective
curve over a finite field.
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

/-- Theorem 64.14.3 (Lefschetz Trace Formula). Let `X` be a projective curve
over a finite field `k`, `Λ` a finite ring, and `K` in `D_ctf(X, Λ)`. Then
the global Lefschetz number of `K` equals the local Lefschetz number, i.e.
`Tr(π_X^* | RΓ(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_X | K_x̄)` in `Λ♮`.
The global number is `globalLefschetzNumber`; the local number is the
existing stalk-sum `traceGeometricFrobeniusStalks`. Here `X(k)` is identified
with morphisms `𝟙_ ⟶ X`, `π_X^*` is `geometricFrobeniusRGamma`, `RΓ` is
`geometricRGamma`, and `π_X` on stalks is `geometricFrobeniusDerivedStalk`. -/
@[stacks 03TZ]
theorem globalLefschetzNumber_eq_traceGeometricFrobeniusStalks
    (X : SchemeOverField k) [Curve X] [Projective X.hom]
    (K : etaleConstructibleTorFinite Λ X.left) :
    globalLefschetzNumber X K.obj.obj (isPerfect_geometricRGamma X K) =
      traceGeometricFrobeniusStalks X K.obj.obj
        (fun x ↦ isPerfect_geometricDerivedStalk K x) :=
  sorry

end AlgebraicGeometry.SchemeOverField
