/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
import StacksCheckRecall

@[expose] public section

/-!
# Definition 33.20.1 compatibility entry point

The reusable predicates for algebraic and locally algebraic schemes over a
field are owned by `ReasLib.AlgebraicGeometry.Scheme.Algebraic`.
-/

universe u

/- Definition 33.20.1 (1): An algebraic scheme over a field has a structure morphism of finite
type. -/
@[stacks 06LG] #check
  (AlgebraicGeometry.algebraic_iff_finiteType :
    ∀ {k : Type u} [Field k]
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))),
      AlgebraicGeometry.Algebraic X ↔ AlgebraicGeometry.Scheme.Hom.FiniteType X.hom)

/- Definition 33.20.1 (2): A locally algebraic scheme over a field has a structure morphism
locally of finite type. -/
@[stacks 06LG] #check
  (AlgebraicGeometry.locallyAlgebraic_iff_locallyOfFiniteType :
    ∀ {k : Type u} [Field k]
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))),
      AlgebraicGeometry.LocallyAlgebraic X ↔ AlgebraicGeometry.LocallyOfFiniteType X.hom)
