/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.MvPolynomial
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Variety

/-!
# Regular rational-function hypersurfaces in positive characteristic

This file packages two affine hypersurfaces over `RatFunc (ZMod p)` and records
their regularity and geometric reducedness or normality properties.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.RationalFunctionRegularityCounterexample

/-- The rational function field `𝔽_p(t)` in characteristic `p`. -/
abbrev BaseField (p : ℕ) [Fact p.Prime] : Type :=
  RatFunc (ZMod p)

namespace InseparablePoint

/-- The polynomial `x ^ p - t` over `𝔽_p(t)`. -/
abbrev polynomial (p : ℕ) [Fact p.Prime] : Polynomial (BaseField p) :=
  Polynomial.X ^ p - Polynomial.C (RatFunc.X : BaseField p)

/-- The quotient `𝔽_p(t)[x] / (x ^ p - t)`. -/
abbrev CoordinateRing (p : ℕ) [Fact p.Prime] : Type :=
  Polynomial (BaseField p) ⧸
    Ideal.span ({polynomial p} : Set (Polynomial (BaseField p)))

/-- The spectrum of `𝔽_p(t)[x] / (x ^ p - t)`. -/
def scheme (p : ℕ) [Fact p.Prime] : Scheme :=
  Spec (CommRingCat.of (CoordinateRing p))

/-- The canonical structure morphism from `Spec(𝔽_p(t)[x] / (x ^ p - t))`
to `Spec(𝔽_p(t))`. -/
def toBase (p : ℕ) [Fact p.Prime] :
    scheme p ⟶ Spec (CommRingCat.of (BaseField p)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (BaseField p) (CoordinateRing p)))

/-- The hypersurface `x ^ p = t` as a scheme over `𝔽_p(t)`. -/
def overBase (p : ℕ) [Fact p.Prime] :
    Over (Spec (CommRingCat.of (BaseField p))) :=
  Over.mk (toBase p)

/-- The coordinate ring `𝔽_p(t)[x] / (x ^ p - t)` is a domain. -/
instance instIsDomainCoordinateRing (p : ℕ) [Fact p.Prime] :
    IsDomain (CoordinateRing p) := sorry

/-- The hypersurface `x ^ p = t` is a variety over `𝔽_p(t)`. -/
theorem overBase_variety (p : ℕ) [Fact p.Prime] :
    Variety (overBase p) := sorry

/-- The variety structure on the hypersurface `x ^ p = t`. -/
instance instVarietyOverBase (p : ℕ) [Fact p.Prime] :
    Variety (overBase p) :=
  overBase_variety p

/-- The affine scheme `Spec(𝔽_p(t)[x] / (x ^ p - t))` is regular. -/
theorem scheme_regular (p : ℕ) [Fact p.Prime] :
    Scheme.Regular (scheme p) := sorry

/-- The canonical regular scheme structure on `Spec(𝔽_p(t)[x] / (x ^ p - t))`. -/
instance instRegularScheme (p : ℕ) [Fact p.Prime] :
    Scheme.Regular (scheme p) :=
  scheme_regular p

/-- The algebra `𝔽_p(t)[x] / (x ^ p - t)` is not geometrically reduced over
`𝔽_p(t)`. -/
theorem coordinateRing_not_isGeometricallyReduced (p : ℕ) [Fact p.Prime] :
    ¬ Algebra.IsGeometricallyReduced (BaseField p) (CoordinateRing p) := sorry

/-- The hypersurface `x ^ p = t` is not geometrically reduced over `𝔽_p(t)`. -/
theorem overBase_not_geometricallyReduced (p : ℕ) [Fact p.Prime] :
    ¬ SchemeOverField.geometricallyReduced (overBase p) := sorry

end InseparablePoint

namespace Cusp

/-- The polynomial `y ^ 2 - x ^ p + t` over `𝔽_p(t)`, with `x = X 0` and
`y = X 1`. -/
abbrev equation (p : ℕ) [Fact p.Prime] :
    MvPolynomial (Fin 2) (BaseField p) :=
  MvPolynomial.X (1 : Fin 2) ^ 2 -
    MvPolynomial.X (0 : Fin 2) ^ p +
    MvPolynomial.C (RatFunc.X : BaseField p)

/-- The quotient `𝔽_p(t)[x, y] / (y ^ 2 - x ^ p + t)`. -/
abbrev CoordinateRing (p : ℕ) [Fact p.Prime] : Type :=
  MvPolynomial (Fin 2) (BaseField p) ⧸
    Ideal.span ({equation p} : Set (MvPolynomial (Fin 2) (BaseField p)))

/-- The spectrum of `𝔽_p(t)[x, y] / (y ^ 2 - x ^ p + t)`. -/
def scheme (p : ℕ) [Fact p.Prime] : Scheme :=
  Spec (CommRingCat.of (CoordinateRing p))

/-- The canonical structure morphism from the cusp hypersurface to
`Spec(𝔽_p(t))`. -/
def toBase (p : ℕ) [Fact p.Prime] :
    scheme p ⟶ Spec (CommRingCat.of (BaseField p)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (BaseField p) (CoordinateRing p)))

/-- The cusp hypersurface `y ^ 2 - x ^ p + t = 0` as a scheme over `𝔽_p(t)`. -/
def overBase (p : ℕ) [Fact p.Prime] :
    Over (Spec (CommRingCat.of (BaseField p))) :=
  Over.mk (toBase p)

/-- If `2 < p`, the coordinate ring of the cusp hypersurface is a domain. -/
theorem coordinateRing_isDomain (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    IsDomain (CoordinateRing p) := sorry

/-- The canonical domain structure on the cusp coordinate ring in
characteristic greater than two. -/
instance instIsDomainCoordinateRing (p : ℕ) [Fact p.Prime] [Fact (2 < p)] :
    IsDomain (CoordinateRing p) :=
  coordinateRing_isDomain p (Fact.out : 2 < p)

/-- If `2 < p`, the cusp hypersurface is a variety over `𝔽_p(t)`. -/
theorem overBase_variety (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    Variety (overBase p) := sorry

/-- The variety structure on the cusp hypersurface in characteristic greater
than two. -/
instance instVarietyOverBase (p : ℕ) [Fact p.Prime] [Fact (2 < p)] :
    Variety (overBase p) :=
  overBase_variety p (Fact.out : 2 < p)

/-- If `2 < p`, the cusp hypersurface is regular. -/
theorem scheme_regular (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    Scheme.Regular (scheme p) := sorry

/-- The canonical regular scheme structure on the cusp hypersurface in
characteristic greater than two. -/
instance instRegularScheme (p : ℕ) [Fact p.Prime] [Fact (2 < p)] :
    Scheme.Regular (scheme p) :=
  scheme_regular p (Fact.out : 2 < p)

/-- If `2 < p`, the cusp coordinate ring is geometrically reduced over
`𝔽_p(t)`. -/
theorem coordinateRing_isGeometricallyReduced (p : ℕ) [Fact p.Prime]
    (hp : 2 < p) :
    Algebra.IsGeometricallyReduced (BaseField p) (CoordinateRing p) := sorry

/-- The canonical geometrically reduced algebra structure on the cusp
coordinate ring in characteristic greater than two. -/
instance instIsGeometricallyReducedCoordinateRing
    (p : ℕ) [Fact p.Prime] [Fact (2 < p)] :
    Algebra.IsGeometricallyReduced (BaseField p) (CoordinateRing p) :=
  coordinateRing_isGeometricallyReduced p (Fact.out : 2 < p)

/-- If `2 < p`, the cusp hypersurface is geometrically reduced over `𝔽_p(t)`. -/
theorem overBase_geometricallyReduced (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    SchemeOverField.geometricallyReduced (overBase p) := sorry

/-- If `2 < p`, the cusp coordinate ring is not geometrically normal over
`𝔽_p(t)`. -/
theorem coordinateRing_not_isGeometricallyNormal (p : ℕ) [Fact p.Prime]
    (hp : 2 < p) :
    ¬ Algebra.IsGeometricallyNormal (BaseField p) (CoordinateRing p) := sorry

/-- If `2 < p`, the cusp hypersurface is not geometrically normal over
`𝔽_p(t)`. -/
theorem overBase_not_geometricallyNormal (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    ¬ SchemeOverField.geometricallyNormal (overBase p) := sorry

end Cusp

end AlgebraicGeometry.RationalFunctionRegularityCounterexample
