module

public import stacks_project.Chap90.Definition_90_17_1_ObjectLift
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lifts of objects indexed by the source algebra

When the map `f : A' ⟶ A` is the given map in context, the category and the set of
lifts of `x` along `f` may be written in terms of `A'`.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- Remark 90.17.2 (1): when the map `f : A' ⟶ A` is the given map in context, the
category of lifts of `x` along `f` may be written as the category of lifts of `x`
to `A'`. This is `liftCatOver p x A' f`, still depending on the given `f`. -/
@[stacks 06JF]
abbrev liftCatOver (p : F ⥤ ArtinianLocalAlgCat Λ k) {A : ArtinianLocalAlgCat Λ k}
    (x : p.Fiber A) (A' : ArtinianLocalAlgCat Λ k) (f : A' ⟶ A) :=
  ObjectLift p f x

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
/-- The `A'`-first spelling of the lift category is the `f`-indexed lift category. -/
theorem liftCatOver_eq (p : F ⥤ ArtinianLocalAlgCat Λ k) {A : ArtinianLocalAlgCat Λ k}
    (x : p.Fiber A) (A' : ArtinianLocalAlgCat Λ k) (f : A' ⟶ A) :
    liftCatOver p x A' f = ObjectLift p f x :=
  rfl

/-- Remark 90.17.2 (2): when the map `f : A' ⟶ A` is the given map in context, the
set of isomorphism classes of lifts of `x` along `f` may be written as the set of
lifts of `x` to `A'`. This is `liftIsoClassesOver p x A' f`, still depending on the
given `f`. -/
@[stacks 06JF]
abbrev liftIsoClassesOver (p : F ⥤ ArtinianLocalAlgCat Λ k) {A : ArtinianLocalAlgCat Λ k}
    (x : p.Fiber A) (A' : ArtinianLocalAlgCat Λ k) (f : A' ⟶ A) :=
  lifts p f x

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
/-- The `A'`-first spelling of the set of lifts is the `f`-indexed set of isomorphism
classes. -/
theorem liftIsoClassesOver_eq (p : F ⥤ ArtinianLocalAlgCat Λ k)
    {A : ArtinianLocalAlgCat Λ k} (x : p.Fiber A) (A' : ArtinianLocalAlgCat Λ k)
    (f : A' ⟶ A) : liftIsoClassesOver p x A' f = lifts p f x :=
  rfl

end CategoryTheory.Functor
