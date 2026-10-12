/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.Trace
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Characteristic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import stacks_project.Chap59.«59_56_0_1»
public import stacks_project.Chap59.Definition_59_29_1_GeometricPoint
public import stacks_project.Chap64.Definition_64_3_4_GeometricFrobenius

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]

/-- A scheme over a field of characteristic `p` has characteristic `p`. -/
instance instIsCharP (X : SchemeOverField k) : Scheme.IsCharP X.left p :=
  isCharP_of_target X.hom

/-- The exponent `f` such that `#k = p ^ f`. -/
def finiteFieldRank (k : Type u) [Field k] [Fintype k] (p : ℕ) [Fact p.Prime]
    [CharP k p] [Algebra (ZMod p) k] : ℕ :=
  Module.finrank (ZMod p) k

/-- Geometric Frobenius of `X / k` with the canonical exponent `Module.finrank (ZMod p) k`. -/
abbrev geometricFrobenius_ofFiniteField [Fintype k] (X : SchemeOverField k) : X.left ⟶ X.left :=
  geometricFrobenius p (finiteFieldRank k p) X

/-- Geometric Frobenius over `k` with the canonical finite-field exponent. -/
abbrev geometricFrobeniusOver_ofFiniteField [Fintype k] (X : SchemeOverField k) : X ⟶ X :=
  geometricFrobeniusOver p (finiteFieldRank k p)
    (FiniteField.pow_finrank_eq_card p k).symm X

/-- Arithmetic Frobenius of `AlgebraicClosure k`, as the `q`-power automorphism. -/
def arithmeticFrobeniusEquiv [Fintype k] : Gal(AlgebraicClosure k/k) :=
  AlgEquiv.ofRingEquiv
    (f := iterateFrobeniusEquiv (AlgebraicClosure k) p (finiteFieldRank k p))
    (fun _ ↦ sorry)

/-- The spectrum automorphism induced by a Galois element of `AlgebraicClosure k / k`. -/
def specGaloisIso (σ : Gal(AlgebraicClosure k/k)) :
    Spec (CommRingCat.of (AlgebraicClosure k)) ≅
      Spec (CommRingCat.of (AlgebraicClosure k)) where
  hom := FieldExtension.Galois.baseAut k (AlgebraicClosure k) σ
  inv := FieldExtension.Galois.baseAut k (AlgebraicClosure k) σ⁻¹
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The scheme morphism `Spec (AlgebraicClosure k) ⟶ X` lying over a `k`-rational point. -/
def homSpecGeometric {X : SchemeOverField k} (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    Spec (CommRingCat.of (AlgebraicClosure k)) ⟶ X.left :=
  FieldExtension.specMap k (AlgebraicClosure k) ≫ x.left

/-- Galois conjugation of the geometric point lying over a `k`-rational point. -/
def geometricPointGaloisIso {X : SchemeOverField k}
    (x : 𝟙_ (SchemeOverField k) ⟶ X) (σ : Gal(AlgebraicClosure k/k)) :
    Over.mk (homSpecGeometric x) ≅ Over.mk (homSpecGeometric x) :=
  Over.isoMk (specGaloisIso σ) sorry

/-- The geometric point of `X` lying over a `k`-rational point. -/
def geometricPointOfHomSpec {X : SchemeOverField k}
    (x : 𝟙_ (SchemeOverField k) ⟶ X) : Scheme.GeometricPoint X.left :=
  Scheme.GeometricPoint.of (AlgebraicClosure k) (homSpecGeometric x)

/-- The image of the geometric point attached to a rational point. -/
theorem geometricPointOfHomSpec_image {X : SchemeOverField k}
    (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    (geometricPointOfHomSpec x).image =
      x.left (IsLocalRing.closedPoint k) := sorry

/-- Finiteness of the set of `k`-rational points of a finite-type scheme over a finite field. -/
instance finite_homSpec [Finite k] (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] :
    Finite (𝟙_ (SchemeOverField k) ⟶ X) := sorry

end AlgebraicGeometry.SchemeOverField

namespace AlgebraicGeometry.Scheme.Etale

open SchemeOverField

variable {k : Type u} [Field k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]

/-- The geometric stalk of a small-étale sheaf of `ZMod (ℓ ^ n)`-modules, as a module. -/
def geometricModuleStalk {ℓ n : ℕ} {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n))))
    (s : Spec (CommRingCat.of (AlgebraicClosure k)) ⟶ X) :
    ModuleCat.{u} (ZMod (ℓ ^ n)) :=
  (@Scheme.pointSmallEtale X (AlgebraicClosure k) _
      (@IsSepClosed.of_isAlgClosed (AlgebraicClosure k) _ _) s).presheafFiber.obj F.1

/-- Forgetful comparison between the module-valued geometric stalk and the underlying
type-valued presheaf fibre. -/
def geometricStalkForgetIso {ℓ n : ℕ} {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n))))
    (s : Spec (CommRingCat.of (AlgebraicClosure k)) ⟶ X)
    [PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u} (ZMod (ℓ ^ n))))] :
    (@Scheme.pointSmallEtale X (AlgebraicClosure k) _
        (@IsSepClosed.of_isAlgClosed (AlgebraicClosure k) _ _) s).presheafFiber.obj
        (F.1 ⋙ CategoryTheory.forget (ModuleCat.{u} (ZMod (ℓ ^ n)))) ≅
      (CategoryTheory.forget (ModuleCat.{u} (ZMod (ℓ ^ n)))).obj (geometricModuleStalk F s) :=
  ((@Scheme.pointSmallEtale X (AlgebraicClosure k) _
      (@IsSepClosed.of_isAlgClosed (AlgebraicClosure k) _ _) s).presheafFiberCompIso
    (CategoryTheory.forget (ModuleCat.{u} (ZMod (ℓ ^ n))))).app F.1

/-- Geometric Frobenius on a geometric stalk, as the Galois action of the inverse of
arithmetic Frobenius. -/
def geometricFrobeniusStalk {ℓ n : ℕ} [Fintype k] {X : SchemeOverField k}
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n))))
    (x : 𝟙_ (SchemeOverField k) ⟶ X)
    [PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u} (ZMod (ℓ ^ n))))] :
    geometricModuleStalk F (homSpecGeometric x) →ₗ[ZMod (ℓ ^ n)]
      geometricModuleStalk F (homSpecGeometric x) where
  toFun :=
    let s := homSpecGeometric x
    let σiso := geometricPointGaloisIso x arithmeticFrobeniusEquiv⁻¹
    let Ftype := F.1 ⋙ CategoryTheory.forget (ModuleCat.{u} (ZMod (ℓ ^ n)))
    let e := geometricStalkForgetIso F s
    fun m ↦ e.hom (stalkGaloisAction s σiso Ftype (e.inv m))
  map_add' := sorry
  map_smul' := sorry

/-- Evaluating geometric Frobenius on a geometric stalk recovers the Galois action of
the inverse of arithmetic Frobenius. -/
theorem geometricFrobeniusStalk_apply {ℓ n : ℕ} [Fintype k] {X : SchemeOverField k}
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n))))
    (x : 𝟙_ (SchemeOverField k) ⟶ X)
    [PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u} (ZMod (ℓ ^ n))))]
    (m : geometricModuleStalk F (homSpecGeometric x)) :
    geometricFrobeniusStalk F x m =
      let s := homSpecGeometric x
      let σiso := geometricPointGaloisIso x arithmeticFrobeniusEquiv⁻¹
      let Ftype := F.1 ⋙ CategoryTheory.forget (ModuleCat.{u} (ZMod (ℓ ^ n)))
      let e := geometricStalkForgetIso F s
      e.hom (stalkGaloisAction s σiso Ftype (e.inv m)) := sorry

end AlgebraicGeometry.Scheme.Etale
