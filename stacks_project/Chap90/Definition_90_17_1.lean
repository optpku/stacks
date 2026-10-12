/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Lifts
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal
import StacksCheckRecall

/-!
# Lifts of objects in a category cofibered in groupoids

The category of lifts of a fibre object along a morphism of `ArtinianLocalAlgCat`,
and the type of isomorphism classes of those lifts.
-/

@[expose] public section

open CategoryTheory
open Functor

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
variable {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A) (x : p.Fiber A)

/- Definition 90.17.1 (1): the category of lifts of `x` along `f` has objects the
morphisms `x' ⟶ x` lying over `f`, and morphisms the morphisms in the fibre over
`A'` making the over-triangle commute. -/
@[stacks 06JE]
#check (CategoryTheory.Functor.ObjectLift p f x : Type (max v w))

/- Definition 90.17.1 (2): the set of lifts of `x` along `f` is the type of
isomorphism classes of the category of lifts. -/
@[stacks 06JE]
#check (CategoryTheory.Functor.lifts p f x : Type (max v w))
