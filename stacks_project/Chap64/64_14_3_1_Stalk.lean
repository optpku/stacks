/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Point.Category
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import stacks_project.Chap59.Definition_59_77_1
public import stacks_project.Chap59.Lemma_59_29_7
public import stacks_project.Chap59.Lemma_59_71_5
public import stacks_project.Chap59.«59_56_0_1»
public import stacks_project.Chap64.«64_2_0_1_GeometricFrobenius»
public import stacks_project.Chap64.Definition_64_14_1_Comparison
public import stacks_project.Chap64.Proposition_64_10_2_Trace

/-!
# Derived geometric stalks and geometric Frobenius on stalks

This leaf owns the derived geometric stalk `K_x̄` of an étale `Λ`-module
complex and the induced geometric-Frobenius endomorphism `π_X` on that
stalk, via the Galois action of the inverse of arithmetic Frobenius.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
open GrothendieckTopology.Point
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {Λ : Type u} [CommRing Λ]
variable [HasColimitsOfSize.{u, u} (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}},
    HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Small-étale stalk functor of sheaves of `Λ`-modules at the geometric point
of a `k`-rational point. -/
noncomputable def geometricStalkFunctor {X : SchemeOverField k}
    (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ) ⥤ ModuleCat.{u} Λ :=
  ((pointSmallEtale (homSpecGeometric x)).sheafFiber :
    Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ) ⥤ ModuleCat.{u} Λ)

/-- Unfolding of `geometricStalkFunctor` as the small-étale sheaf fibre at
`homSpecGeometric x`. -/
theorem geometricStalkFunctor_eq {X : SchemeOverField k}
    (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    geometricStalkFunctor x =
      ((pointSmallEtale (homSpecGeometric x)).sheafFiber :
        Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ) ⥤ ModuleCat.{u} Λ) :=
  sorry

/-- Small-étale module stalks at a rational geometric point are additive. -/
instance instAdditive_geometricStalkFunctor {X : SchemeOverField k}
    (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    ((geometricStalkFunctor x :
        Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
          ModuleCat.{u} Λ)).Additive :=
  sorry

/-- Small-étale module stalks at a rational geometric point preserve finite
limits. -/
instance instPreservesFiniteLimits_geometricStalkFunctor {X : SchemeOverField k}
    (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    PreservesFiniteLimits
      (geometricStalkFunctor x :
        Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
          ModuleCat.{u} Λ) :=
  sorry

/-- Small-étale module stalks at a rational geometric point preserve finite
colimits. -/
instance instPreservesFiniteColimits_geometricStalkFunctor
    {X : SchemeOverField k} (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    PreservesFiniteColimits
      (geometricStalkFunctor x :
        Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
          ModuleCat.{u} Λ) :=
  sorry

/-- Derived geometric stalk `K_x̄` of an étale `Λ`-module complex at the
geometric point lying over a `k`-rational point. -/
noncomputable def geometricDerivedStalk {X : SchemeOverField k}
    (K : EtaleDerived X.left Λ) (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    DerivedCategory (ModuleCat.{u} Λ) :=
  (ExactFunctor.of (geometricStalkFunctor x)).mapDerivedCategory.obj K

/-- Unfolding of `geometricDerivedStalk` as `mapDerivedCategory` of the
bundled exact small-étale module stalk functor at `homSpecGeometric x`. -/
theorem geometricDerivedStalk_spec {X : SchemeOverField k}
    (K : EtaleDerived X.left Λ) (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    geometricDerivedStalk K x =
      (ExactFunctor.of (geometricStalkFunctor x)).mapDerivedCategory.obj K :=
  sorry

/-- Geometric Frobenius `π_X` on the derived geometric stalk `K_x̄`, as the
Galois action of the inverse of arithmetic Frobenius. -/
noncomputable def geometricFrobeniusDerivedStalk [Fintype k]
    {X : SchemeOverField k} (K : EtaleDerived X.left Λ)
    (x : 𝟙_ (SchemeOverField k) ⟶ X) :
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
theorem geometricFrobeniusDerivedStalk_spec [Fintype k]
    {X : SchemeOverField k} (K : EtaleDerived X.left Λ)
    (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    geometricFrobeniusDerivedStalk K x =
      (ExactFunctor.MapDerivedCategory.map
          (⟨Hom.sheafFiber
              ⟨geometricPointFiberMap (homSpecGeometric x)
                (geometricPointGaloisIso x arithmeticFrobeniusEquiv⁻¹)⟩⟩ :
            ExactFunctor.of (geometricStalkFunctor x) ⟶
              ExactFunctor.of (geometricStalkFunctor x))).app K :=
  sorry

variable [IsNoetherianRing Λ]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension P]
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
    @DerivedTensor.Right.Has (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))
      _ _ _ _ _ _] in
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

end AlgebraicGeometry.SchemeOverField
