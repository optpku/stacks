module

public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Over

/-!
# Object membership for formal coproducts

This leaf owns predicates saying that every component of an ordinary or fixed-target formal
coproduct belongs to a designated collection of objects. It has no site-theoretic dependency.
-/

@[expose] public section

universe w v u v' u'

namespace CategoryTheory
namespace Limits
namespace FormalCoproduct

variable {C : Type u} [Category.{v} C] {U : C}

/-- A formal coproduct lies in `B` when every one of its component objects belongs to `B`. -/
def objectsIn (K : FormalCoproduct.{w} C) (B : Set C) : Prop :=
  ∀ i : K.I, K.obj i ∈ B

/-- Unfolding `objectsIn` quantifies over every component object of the formal coproduct. -/
@[simp] theorem objectsIn_iff (K : FormalCoproduct.{w} C) (B : Set C) :
    K.objectsIn B ↔ ∀ i : K.I, K.obj i ∈ B := sorry

/-- Componentwise mapping preserves membership in a collection when the ambient functor carries
the original collection into the target collection. -/
theorem objectsIn.map
    {D : Type u'} [Category.{v'} D] (F : C ⥤ D) {B : Set C} {B' : Set D}
    {K : FormalCoproduct.{w} C} (hK : K.objectsIn B)
    (hF : ∀ X : C, X ∈ B → F.obj X ∈ B') :
    ((map F).obj K).objectsIn B' := sorry

namespace Over

/-- A fixed-target formal coproduct lies in `B` when every source object of one of its arrows
belongs to `B`. -/
def objectsIn (K : FormalCoproduct.{w} (CategoryTheory.Over U)) (B : Set C) : Prop :=
  ∀ i : K.I, (K.obj i).left ∈ B

/-- Unfolding fixed-target `objectsIn` quantifies over every source object of the family. -/
@[simp] theorem objectsIn_iff (K : FormalCoproduct.{w} (CategoryTheory.Over U)) (B : Set C) :
    objectsIn K B ↔ ∀ i : K.I, (K.obj i).left ∈ B := sorry

/-- The object-membership condition for a fixed-target family built from arrows is pointwise
membership of the supplied source objects. -/
@[simp] theorem ofArrows_objectsIn_iff
    (B : Set C) {I : Type w} (X : I → C) (f : ∀ i : I, X i ⟶ U) :
    objectsIn (ofArrows X f) B ↔ ∀ i : I, X i ∈ B := sorry

end Over

/-- Forgetting the target from a fixed-target formal coproduct converts source-object membership
into ordinary formal-coproduct membership. -/
@[simp] theorem forgetOver_obj_objectsIn_iff {X : C}
    (K : FormalCoproduct.{w} (CategoryTheory.Over X)) (B : Set C) :
    objectsIn ((forgetOver X).obj K) B ↔ Over.objectsIn K B := sorry

end FormalCoproduct
end Limits
end CategoryTheory
