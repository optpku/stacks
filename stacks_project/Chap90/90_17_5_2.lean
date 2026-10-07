module

public import stacks_project.Chap90.«90_17_5_2_LiftsEquiv»
public import stacks_project.Chap90.«90_17_5_2_SelfPullback»
import StacksCheckRecall

/-!
# Lifts of an object to a self fibre product

The displayed comparison `Lift(x, A') × Lift(x, A') ⟶ Lift(x, A' ×_A A')` in the
proof of the free-transitive action of the tangent space on nonempty lift sets.
-/

@[expose] public section

open CategoryTheory
open Functor ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
variable {A A' : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
variable (hf : Function.Surjective f.hom) (x : p.Fiber A)

/- 90.17.5.2: in a category cofibered in groupoids over `ArtinianLocalAlgCat Λ k`
satisfying (RS), a surjection `f : A' ⟶ A` induces a bijection
`Lift(x, A') × Lift(x, A') ⟶ Lift(x, A' ×_A A')` of isomorphism classes of
lifts of `x` along `f` with isomorphism classes of lifts of `x` along
`selfPullbackToBase f`. This is `liftsSelfPullbackEquiv`. -/
@[stacks 06TB]
#check Functor.liftsSelfPullbackEquiv f hf x
