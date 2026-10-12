/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Lifts
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal
import StacksCheckRecall

/-!
# Lifts of objects indexed by the source algebra

When the map `f : A' ⟶ A` is the given map in context, the category and the set of
lifts of `x` along `f` may be written in terms of `A'`. This convention suppresses
the arrow in the notation without removing dependence on `f`.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [CategoryTheory.Functor.IsFibered.InGroupoids p.op]
  {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A) (x : p.Fiber A)

/- Remark 90.17.2 (1): when `f : A' ⟶ A` is understood, the category of lifts of
`x` along `f` may be denoted using `A'`. The suppressed arrow remains an explicit
argument of `CategoryTheory.Functor.ObjectLift p f x`. -/
@[stacks 06JF] #check (CategoryTheory.Functor.ObjectLift p f x : Type (max v w))

/- Remark 90.17.2 (2): when `f : A' ⟶ A` is understood, the set of isomorphism
classes of lifts of `x` along `f` may be denoted using `A'`. The suppressed arrow
remains an explicit argument of `CategoryTheory.Functor.lifts p f x`. -/
@[stacks 06JF] #check (CategoryTheory.Functor.lifts p f x : Type (max v w))

end CategoryTheory.Functor
