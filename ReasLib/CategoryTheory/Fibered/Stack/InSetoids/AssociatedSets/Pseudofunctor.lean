module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids.AssociatedSets.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Associated stacks in sets: pseudofunctorial API

This leaf exposes the bicategorical quotient and the locally discrete target.  The identity and
composition comparisons are the standard `Pseudofunctor.comp` comparisons, stated as whole
isomorphisms so downstream code can rewrite without unfolding the quotient construction.
-/

@[expose] public section

universe uC uS vC vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type uC} [Category.{vC} C]

namespace StackOver.Setoids

variable {J : GrothendieckTopology C}

namespace associatedSets

/-- The associated-sets construction as a pseudofunctor to the locally discrete bicategory of
stacks in sets. It is the canonical composite of the homotopy-category quotient with `functor`,
so its `2`-cell action and coherence are inherited rather than rebuilt. -/
@[stacks 0432 "associated stacks in sets pseudofunctor"]
noncomputable def pseudofunctor (J : GrothendieckTopology C) :
    StackOver.Setoids J ⥤ᵖ LocallyDiscrete (StackOver.Sets J) :=
  (Bicategory.HomotopyCategory.quotient (StackOver.Setoids J)).comp
    (functor J).toPseudofunctor

/-- The associated-sets pseudofunctor has the canonical associated stack as its object action. -/
@[simp, stacks 0432 "associated stack pseudofunctor object action"]
theorem pseudofunctor.obj (X : StackOver.Setoids J) :
    (pseudofunctor J).obj X = LocallyDiscrete.mk X.associatedSets := sorry

/-- The associated-sets pseudofunctor sends a `1`-morphism by the canonical associated-stack
map. -/
@[simp, stacks 0432 "associated stack pseudofunctor morphism action"]
theorem pseudofunctor.map {X Y : StackOver.Setoids J} (F : X ⟶ Y) :
    (pseudofunctor J).map F = (map F).toLoc := sorry

/-- The associated-sets pseudofunctor sends a `2`-morphism to the equality of the induced
associated-stack maps.  Since the target is locally discrete, this equality is the canonical
`eqToHom` between the two identical local morphisms; exposing it avoids forcing consumers to
unfold the homotopy-category quotient. -/
@[simp, stacks 0432 "associated stack pseudofunctor two-cell action"]
theorem pseudofunctor.map₂ {X Y : StackOver.Setoids J} {F G : X ⟶ Y} (eta : F ⟶ G) :
    (pseudofunctor J).map₂ eta =
      eqToHom (congrArg Quiver.Hom.toLoc (map.eq_of_hom eta)) := sorry

/-- The identity comparison of the associated-sets pseudofunctor is the standard comparison
prescribed by `Pseudofunctor.comp`: first the quotient's identity comparison is mapped by the
functor, then the functor's own identity comparison is composed. -/
@[simp, stacks 0432 "associated stacks pseudofunctor identity comparison"]
theorem pseudofunctor.mapId (X : StackOver.Setoids J) :
    (pseudofunctor J).mapId X =
      ((functor J).toPseudofunctor).map₂Iso
          ((Bicategory.HomotopyCategory.quotient (StackOver.Setoids J)).mapId X) ≪≫
        ((functor J).toPseudofunctor).mapId
          ((Bicategory.HomotopyCategory.quotient (StackOver.Setoids J)).obj X) := sorry

/-- The composition comparison of the associated-sets pseudofunctor is the standard comparison
prescribed by `Pseudofunctor.comp`: first the quotient's composition comparison is mapped by the
functor, then the functor's own composition comparison is composed. -/
@[simp, stacks 0432 "associated stacks pseudofunctor composition comparison"]
theorem pseudofunctor.mapComp {X Y Z : StackOver.Setoids J}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    (pseudofunctor J).mapComp F G =
      ((functor J).toPseudofunctor).map₂Iso
          ((Bicategory.HomotopyCategory.quotient (StackOver.Setoids J)).mapComp F G) ≪≫
        ((functor J).toPseudofunctor).mapComp
          ((Bicategory.HomotopyCategory.quotient (StackOver.Setoids J)).map F)
          ((Bicategory.HomotopyCategory.quotient (StackOver.Setoids J)).map G) := sorry

/-- The associated-sets pseudofunctor induces an equivalence on every Hom category. -/
@[stacks 0432 "associated stacks are locally equivalent"]
theorem pseudofunctor.isLocallyEquivalence (J : GrothendieckTopology C) :
    (pseudofunctor J).IsLocallyEquivalence := sorry

/-- Every stack in sets lies in the bicategorical essential image of the associated-sets
pseudofunctor. -/
@[stacks 0432 "associated stacks are essentially surjective"]
theorem pseudofunctor.essSurj (J : GrothendieckTopology C) :
    (pseudofunctor J).EssSurj := sorry

/-- The associated-sets pseudofunctor is a biequivalence from stacks in setoids to the locally
discrete bicategory of stacks in sets. -/
@[stacks 0432 "associated-stacks biequivalence"]
instance pseudofunctor.isBiequivalence (J : GrothendieckTopology C) :
    (pseudofunctor J).IsBiequivalence := sorry

end associatedSets

end StackOver.Setoids

end CategoryTheory
