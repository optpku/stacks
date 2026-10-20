/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import ReasLib.AlgebraicGeometry.Scheme.OverField.ClosedPoints
public import ReasLib.CategoryTheory.Monoidal.Flat
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import stacks_project.Chap59.Definition_59_71_1
public import stacks_project.Chap59.Lemma_59_29_7
public import stacks_project.Chap59.Lemma_59_71_5
public import stacks_project.Chap59.«59_56_0_1»
public import stacks_project.Chap64.«64_2_0_1_GeometricFrobenius»
public import stacks_project.Chap64.Theorem_64_20_1_Finite_Coefficients_Det

/-!
# Local Euler factors of constructible flat étale sheaves

This leaf owns geometric points over closed points, geometric Frobenius on
stalks, and the local Euler factors
`det(1 - π_x^* T^{deg x} | F_x̄)⁻¹` in `Λ⟦T⟧`.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom
open GrothendieckTopology.Point
open scoped AlgebraicGeometry MonoidalCategory PowerSeries.WithPiTopology

namespace PowerSeries.FiniteCoeff

/-- Finite rings carry the discrete topology, so Euler products can be formed in
`R⟦X⟧`. -/
scoped instance instTopologicalSpace (R : Type u) [Finite R] : TopologicalSpace R := ⊥

/-- The topology `instTopologicalSpace` is discrete. -/
scoped instance instDiscreteTopology (R : Type u) [Finite R] : DiscreteTopology R := ⟨rfl⟩

end PowerSeries.FiniteCoeff

open scoped PowerSeries.FiniteCoeff

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {Λ : Type u} [CommRing Λ] [Finite Λ] [IsNoetherianRing Λ]
variable [HasColimitsOfSize.{u, u} (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension F]

/-- A `k`-embedding of the residue field of a closed point into
`AlgebraicClosure k`. -/
def residueFieldEmbedding (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
    (x : closedPoints X.left) :
    (X.left.residueField x.1 : Type u) →ₐ[k] AlgebraicClosure k :=
  IsAlgClosed.lift

/-- The scheme morphism `Spec (AlgebraicClosure k) ⟶ X` lying over a closed
point, induced by `residueFieldEmbedding`. -/
def geometricPointHomOfClosedPoint (X : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom] (x : closedPoints X.left) :
    Spec (.of (AlgebraicClosure k)) ⟶ X.left :=
  Spec.map (CommRingCat.ofHom (residueFieldEmbedding X x).toRingHom) ≫
    X.left.fromSpecResidueField x.1

/-- A geometric point of `X` with values in `AlgebraicClosure k` lying over a
closed point. -/
def geometricPointOfClosedPoint (X : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom] (x : closedPoints X.left) :
    GeometricPoint X.left :=
  GeometricPoint.of (AlgebraicClosure k) (geometricPointHomOfClosedPoint X x)

/-- The image of `geometricPointOfClosedPoint` is the chosen closed point. -/
theorem geometricPointOfClosedPoint_image (X : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom] (x : closedPoints X.left) :
    (geometricPointOfClosedPoint X x).image = x.1 :=
  sorry

/-- Galois conjugation of the geometric point lying over a closed point. -/
def geometricPointGaloisIsoClosed (X : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom] (x : closedPoints X.left)
    (σ : Gal(AlgebraicClosure k/k)) :
    Over.mk (geometricPointHomOfClosedPoint X x) ≅
      Over.mk (geometricPointHomOfClosedPoint X x) :=
  Over.isoMk (specGaloisIso σ) sorry

/-- The geometric stalk of a small-étale sheaf of `Λ`-modules at the chosen
geometric point over a closed point. -/
def geometricStalkClosedPoint {X : SchemeOverField k} [Scheme.Hom.FiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (x : closedPoints X.left) : ModuleCat.{u} Λ :=
  (GeometricPoint.toSmallEtalePoint (geometricPointOfClosedPoint X x)).sheafFiber.obj F

/-- Unfolding of `geometricStalkClosedPoint` as the small-étale sheaf fibre. -/
theorem geometricStalkClosedPoint_spec {X : SchemeOverField k}
    [Scheme.Hom.FiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (x : closedPoints X.left) :
    geometricStalkClosedPoint F x =
      (GeometricPoint.toSmallEtalePoint
        (geometricPointOfClosedPoint X x)).sheafFiber.obj F :=
  sorry

/-- Geometric Frobenius `π_x` on the stalk at a closed point, as the Galois
action of the inverse of arithmetic Frobenius of the residue field. -/
def geometricFrobeniusStalkClosed {X : SchemeOverField k}
    [Scheme.Hom.FiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (x : closedPoints X.left) :
    Module.End Λ (geometricStalkClosedPoint F x) :=
  ModuleCat.Hom.hom
    ((Hom.sheafFiber
        ⟨geometricPointFiberMap (geometricPointHomOfClosedPoint X x)
          (geometricPointGaloisIsoClosed X x
            ((FiniteField.arithmeticFrobenius k)⁻¹ ^ X.hom.residueDegree x.1))⟩).app F)

/-- Evaluating geometric Frobenius on a closed-point stalk recovers the Galois
action of the residue-field arithmetic Frobenius. -/
theorem geometricFrobeniusStalkClosed_spec {X : SchemeOverField k}
    [Scheme.Hom.FiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (x : closedPoints X.left) :
    geometricFrobeniusStalkClosed F x =
      ModuleCat.Hom.hom
        ((Hom.sheafFiber
            ⟨geometricPointFiberMap (geometricPointHomOfClosedPoint X x)
              (geometricPointGaloisIsoClosed X x
                ((FiniteField.arithmeticFrobenius k)⁻¹ ^
                  X.hom.residueDegree x.1))⟩).app F) :=
  sorry

variable [∀ {Y : Scheme.{u}},
    MonoidalCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Stalks of constructible flat étale `Λ`-module sheaves at closed points are
finite `Λ`-modules. -/
theorem finite_stalkClosedPoint {X : SchemeOverField k}
    [Scheme.Hom.FiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hF : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [MonoidalCategory.IsFlat F] (x : closedPoints X.left) :
    Module.Finite Λ (geometricStalkClosedPoint F x) :=
  sorry

/-- Stalks of constructible flat étale `Λ`-module sheaves at closed points are
projective `Λ`-modules. -/
theorem projective_stalkClosedPoint {X : SchemeOverField k}
    [Scheme.Hom.FiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hF : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [MonoidalCategory.IsFlat F] (x : closedPoints X.left) :
    Module.Projective Λ (geometricStalkClosedPoint F x) :=
  sorry

/-- The local Euler factor
`det(1 - π_x^* T^{deg x} | F_x̄)⁻¹` at a closed point. -/
def localEulerFactor {X : SchemeOverField k} [Scheme.Hom.FiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (x : closedPoints X.left)
    [Module.Finite Λ (geometricStalkClosedPoint F x)]
    [Module.Projective Λ (geometricStalkClosedPoint F x)] : PowerSeries Λ :=
  PowerSeries.invOfUnit
    (PowerSeries.substXPow (X.hom.residueDegree x.1)
      (LinearMap.FiniteProjective.detOneSubT (geometricFrobeniusStalkClosed F x)))
    1

/-- Unfolding of the local Euler factor as the inverse reverse characteristic
series of geometric Frobenius, after substituting `T ↦ T^{deg x}`. -/
theorem localEulerFactor_spec {X : SchemeOverField k}
    [Scheme.Hom.FiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (x : closedPoints X.left)
    [Module.Finite Λ (geometricStalkClosedPoint F x)]
    [Module.Projective Λ (geometricStalkClosedPoint F x)] :
    localEulerFactor F x =
      PowerSeries.invOfUnit
        (PowerSeries.substXPow (X.hom.residueDegree x.1)
          (LinearMap.FiniteProjective.detOneSubT
            (geometricFrobeniusStalkClosed F x)))
        1 :=
  sorry

/-- The local Euler factor depends only on the underlying closed point. -/
theorem localEulerFactor_independent {X : SchemeOverField k}
    [Scheme.Hom.FiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (x y : closedPoints X.left) (hxy : x.1 = y.1)
    [Module.Finite Λ (geometricStalkClosedPoint F x)]
    [Module.Projective Λ (geometricStalkClosedPoint F x)]
    [Module.Finite Λ (geometricStalkClosedPoint F y)]
    [Module.Projective Λ (geometricStalkClosedPoint F y)] :
    localEulerFactor F x = localEulerFactor F y :=
  sorry

/-- The family of local Euler factors is multipliable in `Λ⟦T⟧`. -/
theorem multipliable_localEulerFactor {X : SchemeOverField k}
    [Scheme.Hom.FiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    [∀ x : closedPoints X.left, Module.Finite Λ (geometricStalkClosedPoint F x)]
    [∀ x : closedPoints X.left, Module.Projective Λ (geometricStalkClosedPoint F x)] :
    Multipliable fun x : closedPoints X.left ↦ localEulerFactor F x :=
  sorry

end AlgebraicGeometry.SchemeOverField
