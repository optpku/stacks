module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap76.Lemma_76_23_7_FiniteFree

/-!
# Finite-freeness of a finitely presented module at a point

If a finitely presented module on an algebraic space is flat at a point over a
locally finitely presented morphism, then flatness of the geometric-fibre stalk,
freeness of that stalk, finite-freeness on an étale neighbourhood in the fibre,
and finite-freeness on an étale neighbourhood in the source are equivalent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 76.23.7: Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` which is locally of finite presentation. Let `F` be a finitely presented
`𝒪_X`-module, and let `x` be a point of `|X|` with image `y = Points.map f x` in `|Y|`.
If `F` is flat at `x` over `Y`, then for a geometric point `xbar` of `X` lying over `x`
with `ybar = xbar.map f` the following are equivalent: the geometric-fibre stalk
`geometricFiberStalk F f xbar` is a flat `geometricFiberRing f xbar`-module; that stalk
is a free `geometricFiberRing f xbar`-module; the pullback of `F` to the geometric fibre
`fieldFiber f (xbar.map f).toFieldValuedPoint` is finite free in an étale neighbourhood
of `geometricFiberPoint f xbar`; and `F` is finite free in an étale neighbourhood of
`x` in `X`. -/
@[stacks 0CZS]
theorem finiteFreeEtaleAt_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] (F : X.Modules)
    [F.IsFinitePresentation] (x : Points X) (xbar : GeometricPoint X)
    (hx : xbar.liesOver x) (h_flat : flatOverAt F f x) :
    List.TFAE
      [geometricFiberStalk_isFlat F f xbar, geometricFiberStalk_isFree F f xbar,
        finiteFreeEtaleAt_fiber F f xbar, finiteFreeEtaleAt F x] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
