/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupportTrace
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
import StacksCheckRecall

/-!
# Local Lefschetz number

The sum of traces of geometric Frobenius on derived geometric stalks of a
complex of étale `Λ`-modules at `k`-rational points, valued in `Λ♮`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry MonoidalCategory Ring

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {Λ : Type u} [Ring Λ] [Finite Λ]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}},
    HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ {Y : Scheme.{u}},
    ((sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
      (Opposite.op (Etale.globalEtale Y))).Additive]
variable [∀ {Y : Scheme.{u}},
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
          (Opposite.op (Etale.globalEtale Y))))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z),
    ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
      Z.smallEtaleTopology Y.smallEtaleTopology).Additive]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z),
    PreservesFiniteLimits
      ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
        Z.smallEtaleTopology Y.smallEtaleTopology)]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z),
    PreservesFiniteColimits
      ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
        Z.smallEtaleTopology Y.smallEtaleTopology)]
variable [∀ {A B C : Scheme.{u}} (f : B ⟶ A) (g : C ⟶ B),
    (((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
        A.smallEtaleTopology B.smallEtaleTopology) ⋙
      ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
        B.smallEtaleTopology C.smallEtaleTopology)).Additive]
variable [∀ {A B C : Scheme.{u}} (f : B ⟶ A) (g : C ⟶ B),
    PreservesFiniteLimits
      (((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
          A.smallEtaleTopology B.smallEtaleTopology) ⋙
        ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
          B.smallEtaleTopology C.smallEtaleTopology))]
variable [∀ {A B C : Scheme.{u}} (f : B ⟶ A) (g : C ⟶ B),
    PreservesFiniteColimits
      (((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
          A.smallEtaleTopology B.smallEtaleTopology) ⋙
        ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
          B.smallEtaleTopology C.smallEtaleTopology))]
variable (X : SchemeOverField k) [Curve X] [Projective X.hom]

/- Definition 64.14.2. Let `Λ` be a finite ring, `X` a projective curve over a
finite field `k`, and `K` an object of `D_ctf(X, Λ)`, as in Definition 64.14.1.
Since `K` lies in `D_ctf(X, Λ)`, for any geometric point `x̄` of `X` the
complex `K_x̄` is perfect in `D_perf(Λ)`. The Frobenius `π_X` acts on
`K_x̄`. The local Lefschetz number of `K` is the sum
`∑_{x ∈ X(k)} Tr(π_x | K_x̄)`, again an element of `Λ♮`.
Here `X(k)` is the type `𝟙_ ⟶ X`. The canonical derived geometric stalks and
their geometric Frobenius endomorphisms use inverse arithmetic Frobenius.
The canonical definition extends to any complex with perfect geometric stalks;
this perfectness condition is not an identification with `D_ctf`. The last
check supplies the perfectness required for the source's constructible
Tor-finite complexes. Since a projective curve over a finite field has finitely
many rational points, the canonical `finsum` is the ordinary finite sum. -/
@[stacks 03TY] #check
  (AlgebraicGeometry.SchemeOverField.CompactSupportTrace.traceGeometricFrobeniusStalks
    (X := X) (Λ := Λ) :
    ∀ (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
      (hK : ∀ x : (𝟙_ (SchemeOverField k) ⟶ X),
        DerivedCategory.IsPerfect (CompactSupportTrace.geometricDerivedStalk (Λ := Λ) K x)), Λ♮)

#check
  (AlgebraicGeometry.SchemeOverField.CompactSupportTrace.traceGeometricFrobeniusStalks_spec
    (X := X) (Λ := Λ) :
    ∀ (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
      (hK : ∀ x : (𝟙_ (SchemeOverField k) ⟶ X),
        DerivedCategory.IsPerfect (CompactSupportTrace.geometricDerivedStalk (Λ := Λ) K x)),
      CompactSupportTrace.traceGeometricFrobeniusStalks (Λ := Λ) K hK =
        ∑ᶠ x : (𝟙_ (SchemeOverField k) ⟶ X),
          (hK x).traceNatural (CompactSupportTrace.geometricFrobeniusDerivedStalk (Λ := Λ) K x))

#check
  (AlgebraicGeometry.SchemeOverField.CompactSupportTrace.isPerfect_geometricDerivedStalk_of_finiteRing
    (X := X) (Λ := Λ) :
    ∀ (K : Scheme.Etale.Derived.FiniteRing.ConstructibleTorFinite
        (X := X.left) (Λ := Λ))
      (x : 𝟙_ (SchemeOverField k) ⟶ X),
      DerivedCategory.IsPerfect (CompactSupportTrace.geometricDerivedStalk (Λ := Λ) K.obj x))

end AlgebraicGeometry.SchemeOverField
