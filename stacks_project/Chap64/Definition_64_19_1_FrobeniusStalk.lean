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
public import stacks_project.Chap59.Definition_59_71_1
public import stacks_project.Chap59.Definition_59_77_1
public import stacks_project.Chap59.Lemma_59_29_7
public import stacks_project.Chap59.Lemma_59_71_5
public import stacks_project.Chap59.«59_56_0_1»
public import stacks_project.Chap64.«64_2_0_1_GeometricFrobenius»

/-!
# Geometric Frobenius on stalks at closed points

This leaf owns the canonical geometric point over a closed point of a
finite-type scheme over a finite field, and the action of residue-field
geometric Frobenius on small-étale and derived stalks.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
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
  -- Local instance justification (proof-local temporary data): `CharP` has an out-param, so the characteristic of κ(x) cannot be a global instance from `CharP k p`.
  haveI : CharP (X.left.residueField x.1) p := charP_residueField X x.1
  AlgEquiv.ofRingEquiv
    (f := iterateFrobeniusEquiv (AlgebraicClosure (X.left.residueField x.1)) p
      (Module.finrank (ZMod p) (X.left.residueField x.1)))
    (fun _ ↦ sorry)

/-- The spectrum automorphism induced by a Galois element of
`AlgebraicClosure K / K`. -/
def specGaloisIsoClosed {K : Type u} [Field K] (σ : Gal(AlgebraicClosure K/K)) :
    Spec (CommRingCat.of (AlgebraicClosure K)) ≅
      Spec (CommRingCat.of (AlgebraicClosure K)) where
  hom := FieldExtension.Galois.baseAut K (AlgebraicClosure K) σ
  inv := FieldExtension.Galois.baseAut K (AlgebraicClosure K) σ⁻¹
  hom_inv_id := sorry
  inv_hom_id := sorry

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

/-- The source field of the canonical geometric point over a closed point is
algebraically closed. -/
instance instIsAlgClosed_geometricPointOverClosedPoint (X : SchemeOverField k)
    (x : closedPoints X.left) :
    IsAlgClosed (geometricPointOverClosedPoint X x).K :=
  (geometricPointOverClosedPoint X x).isAlgClosed

/-- The source field of the canonical geometric point over a closed point is
separably closed. -/
instance instIsSepClosed_geometricPointOverClosedPoint (X : SchemeOverField k)
    (x : closedPoints X.left) :
    IsSepClosed (geometricPointOverClosedPoint X x).K :=
  @IsSepClosed.of_isAlgClosed _ _
    (geometricPointOverClosedPoint X x).isAlgClosed

/-- Galois conjugation of the canonical geometric point over a closed point. -/
def geometricPointGaloisIsoClosed [Fintype k] (X : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom] (x : closedPoints X.left)
    (σ : Gal(AlgebraicClosure (X.left.residueField x.1)/X.left.residueField x.1)) :
    Over.mk (geometricPointOverClosedPoint X x).hom ≅
      Over.mk (geometricPointOverClosedPoint X x).hom :=
  Over.isoMk (specGaloisIsoClosed σ) sorry

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
        ⟨geometricPointFiberMap (geometricPointOverClosedPoint X x).hom
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
            ⟨geometricPointFiberMap (geometricPointOverClosedPoint X x).hom
              (geometricPointGaloisIsoClosed X x
                (arithmeticFrobeniusEquivClosed X x)⁻¹)⟩).app F) := sorry

/-- The closed point underlying a `k`-rational point. -/
def closedPointOfRationalPoint {X : SchemeOverField k}
    [Scheme.Hom.FiniteType X.hom] (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    closedPoints X.left :=
  ⟨x.left (IsLocalRing.closedPoint k), sorry⟩

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
    (K : EtaleDerived X.left Λ) (x : closedPoints X.left) :
    DerivedCategory (ModuleCat.{u} Λ) :=
  (ExactFunctor.of (geometricStalkFunctorClosed (Λ := Λ) x)).mapDerivedCategory.obj K

/-- Unfolding of `geometricDerivedStalkClosed` as `mapDerivedCategory` of the
closed-point stalk functor. -/
theorem geometricDerivedStalkClosed_spec {X : SchemeOverField k}
    (K : EtaleDerived X.left Λ) (x : closedPoints X.left) :
    geometricDerivedStalkClosed K x =
      (ExactFunctor.of (geometricStalkFunctorClosed (Λ := Λ) x)).mapDerivedCategory.obj
        K := sorry

/-- Geometric Frobenius `π_x` on a derived geometric stalk at a closed point,
as the Galois action of the inverse of residue-field arithmetic Frobenius. -/
def geometricFrobeniusDerivedStalkClosed [Fintype k] {X : SchemeOverField k}
    [Scheme.Hom.FiniteType X.hom] (K : EtaleDerived X.left Λ)
    (x : closedPoints X.left) :
    End (geometricDerivedStalkClosed K x) :=
  let τ : geometricStalkFunctorClosed (Λ := Λ) x ⟶
      geometricStalkFunctorClosed (Λ := Λ) x :=
    Hom.sheafFiber
      ⟨geometricPointFiberMap (geometricPointOverClosedPoint X x).hom
        (geometricPointGaloisIsoClosed X x
          (arithmeticFrobeniusEquivClosed X x)⁻¹)⟩
  (ExactFunctor.MapDerivedCategory.map
      (⟨τ⟩ : ExactFunctor.of (geometricStalkFunctorClosed (Λ := Λ) x) ⟶
        ExactFunctor.of (geometricStalkFunctorClosed (Λ := Λ) x))).app K

/-- Evaluating geometric Frobenius on a derived closed-point stalk recovers the
derived Galois action of the inverse of residue-field arithmetic Frobenius. -/
theorem geometricFrobeniusDerivedStalkClosed_spec [Fintype k]
    {X : SchemeOverField k} [Scheme.Hom.FiniteType X.hom]
    (K : EtaleDerived X.left Λ) (x : closedPoints X.left) :
    geometricFrobeniusDerivedStalkClosed K x =
      (ExactFunctor.MapDerivedCategory.map
          (⟨Hom.sheafFiber
              ⟨geometricPointFiberMap (geometricPointOverClosedPoint X x).hom
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
    [MonoidalCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
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
