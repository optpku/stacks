module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Tor.Independence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Map

/-!
# Tor independence of algebraic spaces

Two algebraic spaces over a common algebraic space `B` are Tor independent when their
étale local rings at every pair of compatible geometric points are Tor independent over
the corresponding étale local ring of `B`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Two algebraic spaces over a common base are Tor independent when their étale local rings
at every pair of compatible geometric points are Tor independent over the corresponding
étale local ring of the base. -/
def TorIndependentOver {B : AlgebraicSpace S} (X Y : Over B) : Prop :=
  let X₀ := X.left
  let Y₀ := Y.left
  let f := X.hom
  let g := Y.hom
  ∀ (xbar : GeometricPoint X₀) (ybar : GeometricPoint Y₀) (h : xbar.map f = ybar.map g),
    ModuleCat.Tor.IsIndependent
      ((ModuleCat.restrictScalars (etaleLocalRingMap f xbar)).obj
        (ModuleCat.of (etaleLocalRing X₀ xbar) (etaleLocalRing X₀ xbar)))
      (h.symm ▸
        (ModuleCat.restrictScalars (etaleLocalRingMap g ybar)).obj
          (ModuleCat.of (etaleLocalRing Y₀ ybar) (etaleLocalRing Y₀ ybar)))

/-- Geometric-point characterization of Tor independence for algebraic spaces over a common
base: the étale local rings `𝒪_{X, x̄}` and `𝒪_{Y, ȳ}` are Tor independent over
`𝒪_{B, b̄}` whenever `x̄` and `ȳ` form a commutative diagram of geometric points. -/
theorem torIndependentOver_iff {B : AlgebraicSpace S} (X Y : Over B) :
    TorIndependentOver X Y ↔
      let X₀ := X.left
      let Y₀ := Y.left
      let f := X.hom
      let g := Y.hom
      ∀ (xbar : GeometricPoint X₀) (ybar : GeometricPoint Y₀) (h : xbar.map f = ybar.map g),
        ModuleCat.Tor.IsIndependent
          ((ModuleCat.restrictScalars (etaleLocalRingMap f xbar)).obj
            (ModuleCat.of (etaleLocalRing X₀ xbar) (etaleLocalRing X₀ xbar)))
          (h.symm ▸
            (ModuleCat.restrictScalars (etaleLocalRingMap g ybar)).obj
              (ModuleCat.of (etaleLocalRing Y₀ ybar) (etaleLocalRing Y₀ ybar))) :=
  sorry

/-- Tor independence over an algebraic space gives Tor independence of the étale local rings
at any pair of geometric points with the same image in the base. -/
theorem TorIndependentOver.isIndependent {B : AlgebraicSpace S} {X Y : Over B}
    (hXY : TorIndependentOver X Y)
    (xbar : GeometricPoint X.left) (ybar : GeometricPoint Y.left)
    (hxy : xbar.map X.hom = ybar.map Y.hom) :
    ModuleCat.Tor.IsIndependent
      ((ModuleCat.restrictScalars (etaleLocalRingMap X.hom xbar)).obj
        (ModuleCat.of (etaleLocalRing X.left xbar) (etaleLocalRing X.left xbar)))
      (hxy.symm ▸
        (ModuleCat.restrictScalars (etaleLocalRingMap Y.hom ybar)).obj
          (ModuleCat.of (etaleLocalRing Y.left ybar) (etaleLocalRing Y.left ybar))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
