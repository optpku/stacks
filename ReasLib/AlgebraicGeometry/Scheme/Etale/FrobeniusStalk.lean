module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import ReasLib.FieldTheory.Finite.ArithmeticFrobenius
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Etale.StalkGaloisAction
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.FiniteField
public import ReasLib.AlgebraicGeometry.Scheme.OverField.FinitePoints

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u v w

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]

/-- The spectrum automorphism induced by a Galois element of `AlgebraicClosure k / k`. -/
def specGaloisIso (σ : Gal(AlgebraicClosure k/k)) :
    Spec (CommRingCat.of (AlgebraicClosure k)) ≅
      Spec (CommRingCat.of (AlgebraicClosure k)) :=
  Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op

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
  (Scheme.pointSmallEtale s).presheafFiber.obj F.1

/-- Forgetful comparison between the module-valued geometric stalk and the underlying
type-valued presheaf fibre. -/
def geometricStalkForgetIso {ℓ n : ℕ} {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n))))
    (s : Spec (CommRingCat.of (AlgebraicClosure k)) ⟶ X)
    [PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u} (ZMod (ℓ ^ n))))] :
    (Scheme.pointSmallEtale s).presheafFiber.obj
        (F.1 ⋙ CategoryTheory.forget (ModuleCat.{u} (ZMod (ℓ ^ n)))) ≅
      (CategoryTheory.forget (ModuleCat.{u} (ZMod (ℓ ^ n)))).obj (geometricModuleStalk F s) :=
  ((Scheme.pointSmallEtale s).presheafFiberCompIso
    (CategoryTheory.forget (ModuleCat.{u} (ZMod (ℓ ^ n))))).app F.1

/-- The inverse of arithmetic Frobenius induces an endomorphism of the geometric
stalk of a sheaf at a rational point over a finite field. -/
def geometricFrobeniusStalkHom [Fintype k] {A : Type v} [Category.{w} A]
    [HasColimitsOfSize.{u, u} A] {X : SchemeOverField k}
    (F : Sheaf X.left.smallEtaleTopology A)
    (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    (Scheme.pointSmallEtale (homSpecGeometric x)).presheafFiber.obj F.1 ⟶
      (Scheme.pointSmallEtale (homSpecGeometric x)).presheafFiber.obj F.1 :=
  (GrothendieckTopology.Point.Hom.presheafFiber
    (⟨geometricPointFiberMap (homSpecGeometric x)
        (geometricPointGaloisIso x (FiniteField.arithmeticFrobenius k)⁻¹)⟩ :
      Scheme.pointSmallEtale (homSpecGeometric x) ⟶
        Scheme.pointSmallEtale (homSpecGeometric x))).app F.1

/-- Geometric Frobenius sends a canonical germ morphism to the germ morphism whose
pointed lift is transformed by inverse arithmetic Frobenius. -/
theorem geometricFrobeniusStalkHom_toPresheafFiber [Fintype k]
    {A : Type v} [Category.{w} A] [HasColimitsOfSize.{u, u} A] {X : SchemeOverField k}
    (F : Sheaf X.left.smallEtaleTopology A)
    (x : 𝟙_ (SchemeOverField k) ⟶ X) (U : X.left.Etale)
    (t : (Scheme.pointSmallEtale (homSpecGeometric x)).fiber.obj U) :
    let s := homSpecGeometric x
    let σiso := geometricPointGaloisIso x (FiniteField.arithmeticFrobenius k)⁻¹
    (Scheme.pointSmallEtale s).toPresheafFiber U t F.1 ≫ geometricFrobeniusStalkHom F x =
      (Scheme.pointSmallEtale s).toPresheafFiber U
        ((geometricPointFiberMap s σiso).app U t) F.1 := sorry

/-- Geometric Frobenius on a geometric stalk, as the Galois action of the inverse of
arithmetic Frobenius. -/
def geometricFrobeniusStalk {ℓ n : ℕ} [Fintype k] {X : SchemeOverField k}
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n))))
    (x : 𝟙_ (SchemeOverField k) ⟶ X)
    [PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u} (ZMod (ℓ ^ n))))] :
    geometricModuleStalk F (homSpecGeometric x) →ₗ[ZMod (ℓ ^ n)]
      geometricModuleStalk F (homSpecGeometric x) :=
  (geometricFrobeniusStalkHom F x).hom

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
      let σiso := geometricPointGaloisIso x (FiniteField.arithmeticFrobenius k)⁻¹
      let Ftype := F.1 ⋙ CategoryTheory.forget (ModuleCat.{u} (ZMod (ℓ ^ n)))
      let e := geometricStalkForgetIso F s
      e.hom (stalkGaloisAction s σiso Ftype (e.inv m)) := sorry

end AlgebraicGeometry.Scheme.Etale
