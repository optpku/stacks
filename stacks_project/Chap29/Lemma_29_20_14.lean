/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Fiber
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.20.14: if `f : X ⟶ S` is a morphism of schemes of finite type and `s : S`, then
there are only finitely many points of `X` lying over `s` at which `f` is quasi-finite. -/
@[stacks 0AAY] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.finiteQuasiFiniteAtPointsOver :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f] (s : S),
      ({x : X | f x = s ∧ f.QuasiFiniteAt x} : Set X).Finite)
