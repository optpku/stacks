/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.OverField.ClosedPoints
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.Monoidal.Flat
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Etale.FrobeniusStalk

/-!
# Geometric Frobenius on stalks at closed points

This module defines the canonical geometric point over a closed point of a
finite-type scheme over a finite field, and the action of residue-field
geometric Frobenius on small-étale and derived stalks.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open CategoryTheory.MonoidalCategory
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
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}},
    HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [IsNoetherianRing Λ]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension P]

/-- The prime field acts on `κ(x)` through the structure morphism of `X` over `k`. -/
instance residueFieldAlgebra_zmod (X : SchemeOverField k) (x : X.left) :
    Algebra (ZMod p) (X.left.residueField x) :=
  ((algebraMap k (X.left.residueField x)).comp (algebraMap (ZMod p) k)).toAlgebra

/-- The residue field at a point of a scheme in characteristic `p` has
characteristic `p`. -/
theorem charP_residueField (X : SchemeOverField k) (x : X.left) :
    CharP (X.left.residueField x) p := sorry

/-- The residue field at a closed point of a finite-type scheme over a finite
field is finite-dimensional over the prime field. -/
instance instFiniteDimensional_closedPointResidueField_zmod [Fintype k]
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
    (x : closedPoints X.left) :
    FiniteDimensional (ZMod p) (X.left.residueField x.1) := sorry

/-- Arithmetic Frobenius of `AlgebraicClosure κ(x)`, as the `#κ(x)`-power
automorphism. -/
def arithmeticFrobeniusEquivClosed [Fintype k] (X : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom] (x : closedPoints X.left) :
    Gal(AlgebraicClosure (X.left.residueField x.1)/X.left.residueField x.1) :=
  FiniteField.arithmeticFrobenius (X.left.residueField x.1)

/-- The canonical geometric point over a closed point, with source field the
algebraic closure of the residue field. -/
def geometricPointOverClosedPoint (X : SchemeOverField k)
    (x : closedPoints X.left) : GeometricPoint X.left :=
  GeometricPoint.of (AlgebraicClosure (X.left.residueField x.1))
    (Spec.map (CommRingCat.ofHom
        (algebraMap (X.left.residueField x.1)
          (AlgebraicClosure (X.left.residueField x.1)))) ≫
      X.left.fromSpecResidueField x.1)

/-- The image of the canonical geometric point over a closed point is that
closed point. -/
theorem geometricPointOverClosedPoint_image (X : SchemeOverField k)
    (x : closedPoints X.left) :
    (geometricPointOverClosedPoint X x).image = x.1 := sorry

/-- Galois conjugation of the canonical geometric point over a closed point. -/
def geometricPointGaloisIsoClosed [Fintype k] (X : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom] (x : closedPoints X.left)
    (σ : Gal(AlgebraicClosure (X.left.residueField x.1)/X.left.residueField x.1)) :
    Over.mk (geometricPointOverClosedPoint X x).hom ≅
      Over.mk (geometricPointOverClosedPoint X x).hom :=
  Over.isoMk (specGaloisIso σ) (by
    change FieldExtension.Galois.baseAut (X.left.residueField x.1)
      (AlgebraicClosure (X.left.residueField x.1)) σ ≫
      (FieldExtension.specMap (X.left.residueField x.1)
        (AlgebraicClosure (X.left.residueField x.1)) ≫
        X.left.fromSpecResidueField x.1) = _
    rw [← Category.assoc, FieldExtension.Galois.baseAut_over]
    rfl)

/-- Small-étale stalk functor of sheaves of `Λ`-modules at the canonical
geometric point over a closed point. -/
def geometricStalkFunctorClosed {X : SchemeOverField k}
    (x : closedPoints X.left) :
    Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ) ⥤ ModuleCat.{u} Λ :=
  (GeometricPoint.toSmallEtalePoint (geometricPointOverClosedPoint X x)).sheafFiber

/-- Unfolding of `geometricStalkFunctorClosed` as the small-étale sheaf fibre at
the canonical geometric point over `x`. -/
theorem geometricStalkFunctorClosed_eq {X : SchemeOverField k}
    (x : closedPoints X.left) :
    geometricStalkFunctorClosed (Λ := Λ) x =
      (GeometricPoint.toSmallEtalePoint
        (geometricPointOverClosedPoint X x)).sheafFiber := sorry

/-- The geometric stalk of a small-étale sheaf of `Λ`-modules at the canonical
geometric point over a closed point. -/
def geometricStalkClosed {X : SchemeOverField k}
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (x : closedPoints X.left) : ModuleCat.{u} Λ :=
  (geometricStalkFunctorClosed x).obj F

/-- Unfolding of `geometricStalkClosed` as evaluation of the closed-point stalk
functor. -/
theorem geometricStalkClosed_eq {X : SchemeOverField k}
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (x : closedPoints X.left) :
    geometricStalkClosed F x = (geometricStalkFunctorClosed x).obj F := sorry

/-- Geometric Frobenius `π_x` on a geometric stalk at a closed point, as the
Galois action of the inverse of residue-field arithmetic Frobenius. -/
def geometricFrobeniusClosedStalk [Fintype k] {X : SchemeOverField k}
    [Scheme.Hom.FiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (x : closedPoints X.left) :
    geometricStalkClosed F x →ₗ[Λ] geometricStalkClosed F x :=
  ModuleCat.Hom.hom
    ((Hom.sheafFiber
        ⟨geometricPointFiberMap (Ω := AlgebraicClosure (X.left.residueField x.1))
          (geometricPointOverClosedPoint X x).hom
          (geometricPointGaloisIsoClosed X x
            (arithmeticFrobeniusEquivClosed X x)⁻¹)⟩).app F)

/-- Evaluating geometric Frobenius on a closed-point geometric stalk recovers
the Galois action of the inverse of residue-field arithmetic Frobenius. -/
theorem geometricFrobeniusClosedStalk_spec [Fintype k] {X : SchemeOverField k}
    [Scheme.Hom.FiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (x : closedPoints X.left) :
    geometricFrobeniusClosedStalk F x =
      ModuleCat.Hom.hom
        ((Hom.sheafFiber
            ⟨geometricPointFiberMap (Ω := AlgebraicClosure (X.left.residueField x.1))
              (geometricPointOverClosedPoint X x).hom
              (geometricPointGaloisIsoClosed X x
                (arithmeticFrobeniusEquivClosed X x)⁻¹)⟩).app F) := sorry

/-- The closed point underlying a `k`-rational point. -/
def closedPointOfRationalPoint {X : SchemeOverField k}
    [Scheme.Hom.FiniteType X.hom] (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    closedPoints X.left :=
  ⟨x.left (IsLocalRing.closedPoint k), by
    -- Local instance justification (proof-local temporary data): the slice equation identifies this composite with the identity solely inside the closed-point witness proof.
    haveI : LocallyOfFiniteType (x.left ≫ X.hom) := by
      rw [Over.w x]
      change LocallyOfFiniteType (𝟙 (Spec (CommRingCat.of k)))
      infer_instance
    -- Local instance justification (proof-local temporary data): cancellation of the section equation gives finite type of the section, used only by the theorem mapping closed points to closed points below.
    haveI : LocallyOfFiniteType x.left := locallyOfFiniteType_of_comp x.left X.hom
    -- Local instance justification (proof-local temporary data): the finite-type structure morphism makes the scheme Jacobson, used only to construct this closed-point witness.
    haveI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
    exact (Scheme.jacobsonSpace_iff_mapsTo_closedPoints_of_locallyOfFiniteType
      X.left).mp inferInstance x.left (IsLocalRing.isClosed_singleton_closedPoint k)⟩

/-- The canonical geometric point over a `k`-rational closed point has the same
image as the geometric point attached to that rational point. -/
theorem geometricPointOverClosedPoint_of_rationalPoint
    {X : SchemeOverField k} [Scheme.Hom.FiniteType X.hom]
    (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    (geometricPointOverClosedPoint X (closedPointOfRationalPoint x)).image =
      (geometricPointOfHomSpec x).image := sorry

/-- Small-étale module stalks at a closed geometric point are additive. -/
instance instAdditive_geometricStalkFunctorClosed {X : SchemeOverField k}
    (x : closedPoints X.left) :
    ((geometricStalkFunctorClosed (Λ := Λ) x :
        Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
          ModuleCat.{u} Λ)).Additive := sorry

/-- Small-étale module stalks at a closed geometric point preserve finite
limits. -/
instance instPreservesFiniteLimits_geometricStalkFunctorClosed
    {X : SchemeOverField k} (x : closedPoints X.left) :
    PreservesFiniteLimits
      (geometricStalkFunctorClosed (Λ := Λ) x :
        Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
          ModuleCat.{u} Λ) := sorry

/-- Small-étale module stalks at a closed geometric point preserve finite
colimits. -/
instance instPreservesFiniteColimits_geometricStalkFunctorClosed
    {X : SchemeOverField k} (x : closedPoints X.left) :
    PreservesFiniteColimits
      (geometricStalkFunctorClosed (Λ := Λ) x :
        Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
          ModuleCat.{u} Λ) := sorry

/-- Derived geometric stalk `K_x̄` of an étale `Λ`-module complex at the
canonical geometric point over a closed point. -/
def geometricDerivedStalkClosed {X : SchemeOverField k}
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) (x : closedPoints X.left) :
    DerivedCategory (ModuleCat.{u} Λ) :=
  (ExactFunctor.of (geometricStalkFunctorClosed (Λ := Λ) x)).mapDerivedCategory.obj K

/-- Unfolding of `geometricDerivedStalkClosed` as `mapDerivedCategory` of the
closed-point stalk functor. -/
theorem geometricDerivedStalkClosed_spec {X : SchemeOverField k}
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) (x : closedPoints X.left) :
    geometricDerivedStalkClosed K x =
      (ExactFunctor.of (geometricStalkFunctorClosed (Λ := Λ) x)).mapDerivedCategory.obj
        K := sorry

/-- Geometric Frobenius `π_x` on a derived geometric stalk at a closed point,
as the Galois action of the inverse of residue-field arithmetic Frobenius. -/
def geometricFrobeniusDerivedStalkClosed [Fintype k] {X : SchemeOverField k}
    [Scheme.Hom.FiniteType X.hom] (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
    (x : closedPoints X.left) :
    End (geometricDerivedStalkClosed K x) :=
  let τ : geometricStalkFunctorClosed (Λ := Λ) x ⟶
      geometricStalkFunctorClosed (Λ := Λ) x :=
    Hom.sheafFiber
      ⟨geometricPointFiberMap (Ω := AlgebraicClosure (X.left.residueField x.1))
        (geometricPointOverClosedPoint X x).hom
        (geometricPointGaloisIsoClosed X x
          (arithmeticFrobeniusEquivClosed X x)⁻¹)⟩
  (ExactFunctor.MapDerivedCategory.map
      (⟨τ⟩ : ExactFunctor.of (geometricStalkFunctorClosed (Λ := Λ) x) ⟶
        ExactFunctor.of (geometricStalkFunctorClosed (Λ := Λ) x))).app K

/-- Evaluating geometric Frobenius on a derived closed-point stalk recovers the
derived Galois action of the inverse of residue-field arithmetic Frobenius. -/
theorem geometricFrobeniusDerivedStalkClosed_spec [Fintype k]
    {X : SchemeOverField k} [Scheme.Hom.FiniteType X.hom]
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) (x : closedPoints X.left) :
    geometricFrobeniusDerivedStalkClosed K x =
      (ExactFunctor.MapDerivedCategory.map
          (⟨Hom.sheafFiber
              ⟨geometricPointFiberMap (Ω := AlgebraicClosure (X.left.residueField x.1))
                (geometricPointOverClosedPoint X x).hom
                (geometricPointGaloisIsoClosed X x
                  (arithmeticFrobeniusEquivClosed X x)⁻¹)⟩⟩ :
            ExactFunctor.of (geometricStalkFunctorClosed (Λ := Λ) x) ⟶
              ExactFunctor.of (geometricStalkFunctorClosed (Λ := Λ) x))).app K :=
  sorry

/-- Geometric stalks of a constructible étale sheaf of finite type at closed
points are finite modules. -/
theorem finite_geometricStalkClosed {X : SchemeOverField k}
    [Scheme.Hom.FiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hcons : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    (x : closedPoints X.left) :
    Module.Finite Λ (geometricStalkClosed F x) := sorry

/-- Geometric stalks of a constructible flat étale sheaf at closed points are
projective modules. -/
theorem projective_geometricStalkClosed {X : SchemeOverField k}
    [Scheme.Hom.FiniteType X.hom]
    [(X.left.smallEtaleTopology.W (A := ModuleCat.{u} Λ)).IsMonoidal]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hcons : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [MonoidalCategory.IsFlat F] (x : closedPoints X.left) :
    Module.Projective Λ (geometricStalkClosed F x) := sorry

/-- A geometric point lying over a closed point has that closed point as its
image. -/
theorem geometricPoint_image_of_closedPoint {X : SchemeOverField k}
    (x : closedPoints X.left) (s : GeometricPoint X.left)
    (hs : s.image = x.1) :
    s.image = (geometricPointOverClosedPoint X x).image := sorry

end AlgebraicGeometry.SchemeOverField
