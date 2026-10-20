/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Cospan
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.PrecompLift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cospan transformations from explicit precomposition lifts

Two chosen quasi-inverses to precomposition lift the legs of a cartesian cospan through its
three endpoint maps. This is the data-producing step used before applying pseudo-pullback
functoriality; it is independent of stacks and local-equivalence properties.
-/

@[expose] public section

universe u v
universe uX vX uY vY uZ vZ
universe uX' vX' uY' vY' uZ' vZ'

namespace CategoryTheory.CartesianCospanTransform

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {Z : BasedCategory.{vZ, uZ} C}
variable {X' : BasedCategory.{vX', uX'} C}
variable {Y' : BasedCategory.{vY', uY'} C}
variable {Z' : BasedCategory.{vZ', uZ'} C}
variable {iX : CartesianBasedFunctor X.p X'.p}
variable {iZ : CartesianBasedFunctor Z.p Z'.p}

/-- Lift both legs of a cartesian cospan through explicit quasi-inverses to precomposition.
The resulting cospan transformation stores the prescribed endpoint maps, while its target legs
and comparison isomorphisms are the canonical explicit precomposition lifts. -/
@[stacks 04Y1 "explicit componentwise stackification cospan map"]
noncomputable def ofPrecompLifts
    (F : CartesianBasedFunctor X.p Y.p)
    (G : CartesianBasedFunctor Z.p Y.p)
    (iY : CartesianBasedFunctor Y.p Y'.p)
    (qX : Functor.QuasiInverse (CartesianBasedFunctor.precomp Y'.p iX))
    (qZ : Functor.QuasiInverse (CartesianBasedFunctor.precomp Y'.p iZ)) :
    CartesianCospanTransform F G
      ((CartesianBasedFunctor.PrecompLift.mapFunctor iY qX).obj F)
      ((CartesianBasedFunctor.PrecompLift.mapFunctor iY qZ).obj G) where
  left := iX
  right := iZ
  base := iY
  leftIso :=
    (CartesianBasedFunctor.PrecompLift.mapFunctor.comparisonIso iY qX).app F
  rightIso :=
    (CartesianBasedFunctor.PrecompLift.mapFunctor.comparisonIso iY qZ).app G

/-- The left endpoint of the explicit lifted cospan map is the prescribed left map. -/
@[simp, stacks 04Y1 "left endpoint of explicit lifted cospan map"]
theorem ofPrecompLifts.left
    (F : CartesianBasedFunctor X.p Y.p)
    (G : CartesianBasedFunctor Z.p Y.p)
    (iY : CartesianBasedFunctor Y.p Y'.p)
    (qX : Functor.QuasiInverse (CartesianBasedFunctor.precomp Y'.p iX))
    (qZ : Functor.QuasiInverse (CartesianBasedFunctor.precomp Y'.p iZ)) :
    (ofPrecompLifts F G iY qX qZ).left = iX := sorry

/-- The right endpoint of the explicit lifted cospan map is the prescribed right map. -/
@[simp, stacks 04Y1 "right endpoint of explicit lifted cospan map"]
theorem ofPrecompLifts.right
    (F : CartesianBasedFunctor X.p Y.p)
    (G : CartesianBasedFunctor Z.p Y.p)
    (iY : CartesianBasedFunctor Y.p Y'.p)
    (qX : Functor.QuasiInverse (CartesianBasedFunctor.precomp Y'.p iX))
    (qZ : Functor.QuasiInverse (CartesianBasedFunctor.precomp Y'.p iZ)) :
    (ofPrecompLifts F G iY qX qZ).right = iZ := sorry

/-- The common-target component of the explicit lifted cospan map is the prescribed target
map. -/
@[simp, stacks 04Y1 "base endpoint of explicit lifted cospan map"]
theorem ofPrecompLifts.base
    (F : CartesianBasedFunctor X.p Y.p)
    (G : CartesianBasedFunctor Z.p Y.p)
    (iY : CartesianBasedFunctor Y.p Y'.p)
    (qX : Functor.QuasiInverse (CartesianBasedFunctor.precomp Y'.p iX))
    (qZ : Functor.QuasiInverse (CartesianBasedFunctor.precomp Y'.p iZ)) :
    (ofPrecompLifts F G iY qX qZ).base = iY := sorry

/-- The left comparison of the explicit lifted cospan map is the canonical precomposition-lift
comparison. -/
@[simp, stacks 04Y1 "left comparison of explicit lifted cospan map"]
theorem ofPrecompLifts.leftIso
    (F : CartesianBasedFunctor X.p Y.p)
    (G : CartesianBasedFunctor Z.p Y.p)
    (iY : CartesianBasedFunctor Y.p Y'.p)
    (qX : Functor.QuasiInverse (CartesianBasedFunctor.precomp Y'.p iX))
    (qZ : Functor.QuasiInverse (CartesianBasedFunctor.precomp Y'.p iZ)) :
    (ofPrecompLifts F G iY qX qZ).leftIso =
      (CartesianBasedFunctor.PrecompLift.mapFunctor.comparisonIso iY qX).app F := sorry

/-- The right comparison of the explicit lifted cospan map is the canonical
precomposition-lift comparison. -/
@[simp, stacks 04Y1 "right comparison of explicit lifted cospan map"]
theorem ofPrecompLifts.rightIso
    (F : CartesianBasedFunctor X.p Y.p)
    (G : CartesianBasedFunctor Z.p Y.p)
    (iY : CartesianBasedFunctor Y.p Y'.p)
    (qX : Functor.QuasiInverse (CartesianBasedFunctor.precomp Y'.p iX))
    (qZ : Functor.QuasiInverse (CartesianBasedFunctor.precomp Y'.p iZ)) :
    (ofPrecompLifts F G iY qX qZ).rightIso =
      (CartesianBasedFunctor.PrecompLift.mapFunctor.comparisonIso iY qZ).app G := sorry

end CategoryTheory.CartesianCospanTransform

/- Axiom audit: the target legs and comparison isomorphisms are assembled directly from the
two supplied quasi-inverses and the generic explicit precomposition-lift construction. -/
