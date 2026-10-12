/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Quotient
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functors mapping relations on morphisms

This file records the reusable condition that a functor maps one relation on hom-sets into
another.  It is the relation-level analogue of `MorphismProperty.IsMappedBy`.
-/

@[expose] public section

universe uC vC uD vD uE vE

namespace CategoryTheory.HomRel

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {E : Type uE} [Category.{vE} E]

/-- A functor maps `r` into `s` when it sends every pair of `r`-related morphisms to a pair of
`s`-related morphisms. -/
@[stacks 019N "functors mapping relations on morphisms"]
class IsMappedBy (r : HomRel C) (F : C ⥤ D) (s : HomRel D) : Prop where
  /-- Related morphisms have related images. -/
  map_rel {X Y : C} {f g : X ⟶ Y} : r f g → s (F.map f) (F.map g)

/-- An endofunctor preserves a relation on morphisms when it maps that relation into itself. -/
@[stacks 019N "endofunctors preserving a relation on morphisms"]
abbrev IsPreservedBy (r : HomRel C) (F : C ⥤ C) : Prop :=
  IsMappedBy r F r

namespace IsMappedBy

/-- The identity functor maps every relation on morphisms into itself. -/
@[stacks 019N "the identity functor preserves relations on morphisms"]
instance id (r : HomRel C) : IsMappedBy r (𝟭 C) r := sorry

/-- Mapping relations on morphisms is closed under composition of functors. -/
@[stacks 019N "composition of functors mapping relations on morphisms"]
theorem comp (r : HomRel C) (s : HomRel D) (t : HomRel E)
    (F : C ⥤ D) (G : D ⥤ E) (hF : IsMappedBy r F s) (hG : IsMappedBy s G t) :
    IsMappedBy r (F ⋙ G) t := sorry

end IsMappedBy

namespace IsPreservedBy

/-- A composite of endofunctors preserving a relation again preserves that relation. -/
@[stacks 019N "composition of relation-preserving endofunctors"]
instance comp (r : HomRel C) (F G : C ⥤ C)
    [IsPreservedBy r F] [IsPreservedBy r G] :
    IsPreservedBy r (F ⋙ G) := sorry

end IsPreservedBy

namespace quotientFunctor

/-- The composite with the target quotient functor identifies morphisms related by the source
relation. -/
theorem map_rel (r : HomRel C) (F : C ⥤ D) (s : HomRel D) [IsMappedBy r F s]
    (X Y : C) (f g : X ⟶ Y) (h : r f g) :
    (F ⋙ Quotient.functor s).map f = (F ⋙ Quotient.functor s).map g := sorry

end quotientFunctor

/-- A functor mapping `r` into `s` descends to a functor between the corresponding quotient
categories. -/
@[stacks 019N "functor induced between quotient categories by a relation-preserving functor"]
def quotientFunctor (r : HomRel C) (F : C ⥤ D) (s : HomRel D) [IsMappedBy r F s] :
    CategoryTheory.Quotient r ⥤ CategoryTheory.Quotient s :=
  Quotient.lift r (F ⋙ Quotient.functor s) (quotientFunctor.map_rel r F s)

namespace quotientFunctor

/-- The induced quotient functor maps an original object to the image object. -/
@[simp]
theorem obj (r : HomRel C) (F : C ⥤ D) (s : HomRel D) [IsMappedBy r F s] (X : C) :
    (quotientFunctor r F s).obj ((Quotient.functor r).obj X) =
      (Quotient.functor s).obj (F.obj X) := sorry

/-- The induced quotient functor maps the class of a morphism to the class of its image. -/
@[simp]
theorem map (r : HomRel C) (F : C ⥤ D) (s : HomRel D) [IsMappedBy r F s]
    {X Y : C} (f : X ⟶ Y) :
    (quotientFunctor r F s).map ((Quotient.functor r).map f) =
      (Quotient.functor s).map (F.map f) := sorry

end quotientFunctor

end CategoryTheory.HomRel
