/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.Equivalence.QuasiInverse
public import ReasLib.CategoryTheory.Fibered.Stack.CategoryOfElements.Forward
public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.Restriction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Sheaves and category-of-elements stacks

This leaf records the site-specific property comparison for the category-of-elements
construction.  The equivalence of sheaves and stacks in sets is obtained by restricting the
ambient discrete Grothendieck equivalence and then changing from the direct full-subbicategory
presentation to the established nested stack owner.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-! ## Restriction of the discrete Grothendieck equivalence -/

namespace StackOver.Sets

namespace SheafEquivalence

/-- The sheaf condition corresponds to the direct stack property under the specified discrete
Grothendieck equivalence.  This is the only site-specific input to the generic restriction
construction. -/
@[stacks 0430 "sheaf/category-of-elements property comparison"]
theorem property_iff
    (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ Type (max w u)) :
    Presheaf.IsSheaf J F ↔
      IsStack.OnSite.Sets.objectProperty J
        ((FiberedCategoryOver.Sets.PresheafEquivalence.ofEquivalence C).functor.obj F) := sorry

/-- Restriction of the discrete Grothendieck equivalence to sheaves and the direct
full-subbicategory presentation of stacks in sets. -/
@[stacks 0430 "direct sheaf/category-of-elements equivalence"]
noncomputable def directEquivalence (J : GrothendieckTopology C) :
    Sheaf J (Type (max w u)) ≌
      (IsStack.OnSite.Sets.objectProperty J).FullSubbicategory :=
  Equivalence.restrictFullSubbicategory
    (FiberedCategoryOver.Sets.PresheafEquivalence.ofEquivalence C)
    (property_iff J)

namespace directEquivalence

/-- The ambient set-fibred category selected by the forward direct equivalence is the discrete
Grothendieck construction of the underlying presheaf. -/
@[simp, stacks 0430]
theorem functor.obj (J : GrothendieckTopology C)
    (F : Sheaf J (Type (max w u))) :
    ((directEquivalence J).functor.obj F).1 =
      (FiberedCategoryOver.Sets.ofPresheaf C).obj F.1 := sorry

/-- The ambient morphism selected by the forward direct equivalence is the canonical
category-of-elements morphism of the underlying presheaf map. -/
@[simp, stacks 0430]
theorem functor.map (J : GrothendieckTopology C)
    {F G : Sheaf J (Type (max w u))} (f : F ⟶ G) :
    ((directEquivalence J).functor.map f).hom =
      (FiberedCategoryOver.Sets.ofPresheaf C).map f.hom := sorry

/-- The presheaf underlying the inverse direct equivalence is the specified straightening of the
selected category fibred in sets. -/
@[simp, stacks 0430]
theorem inverse.obj (J : GrothendieckTopology C)
    (X : (IsStack.OnSite.Sets.objectProperty J).FullSubbicategory) :
    ((directEquivalence J).inverse.obj X).1 =
      (FiberedCategoryOver.Sets.toPresheaf C).obj X.1 := sorry

/-- The presheaf map underlying the inverse direct equivalence is the specified straightening of
the ambient set-fibred morphism. -/
@[simp, stacks 0430]
theorem inverse.map (J : GrothendieckTopology C)
    {X Y : (IsStack.OnSite.Sets.objectProperty J).FullSubbicategory} (f : X ⟶ Y) :
    ((directEquivalence J).inverse.map f).hom =
      (FiberedCategoryOver.Sets.toPresheaf C).map f.hom := sorry

end directEquivalence

end SheafEquivalence

/-- Set-valued sheaves on `(C, J)` are equivalent to stacks in sets.  The construction is the
object-property restriction of the specified discrete Grothendieck equivalence followed by the
explicit comparison with the established nested stack owner. -/
@[stacks 0430 "sheaves and stacks in sets equivalence"]
noncomputable def sheafEquivalence (J : GrothendieckTopology C) :
    Sheaf J (Type (max w u)) ≌ StackOver.Sets.{u, v, max w u, v} J :=
  (SheafEquivalence.directEquivalence J).trans StackOver.Sets.Restrict.equivalence

namespace sheafEquivalence

/-- The sheaf-to-stack functor is the forward functor of the specified equivalence. -/
@[stacks 0430]
noncomputable abbrev toStack (J : GrothendieckTopology C) :
    Sheaf J (Type (max w u)) ⥤ StackOver.Sets.{u, v, max w u, v} J :=
  (StackOver.Sets.sheafEquivalence J).functor

/-- The stack-to-sheaf functor is the inverse functor of the specified equivalence. -/
@[stacks 0430]
noncomputable abbrev toSheaf (J : GrothendieckTopology C) :
    StackOver.Sets.{u, v, max w u, v} J ⥤ Sheaf J (Type (max w u)) :=
  (StackOver.Sets.sheafEquivalence J).inverse

/-- In the size-saturated universe, the forward functor of `sheafEquivalence` is the
arbitrary-universe `ofSheaf` construction. -/
@[stacks 0430]
theorem toStack_eq_ofSheaf (J : GrothendieckTopology C) :
    toStack J = StackOver.Sets.ofSheaf J := sorry

namespace toStack

/-- Forgetting the stack proof from the sheaf-to-stack image recovers the discrete Grothendieck
construction of the underlying presheaf. -/
@[simp, stacks 0430]
theorem obj.toSets (J : GrothendieckTopology C)
    (F : Sheaf J (Type (max w u))) :
    ((toStack J).obj F).toSets =
      (FiberedCategoryOver.Sets.ofPresheaf C).obj F.1 := sorry

/-- The projection of the sheaf-to-stack image is the opposite category-of-elements projection
of the underlying presheaf. -/
@[simp, stacks 0430]
theorem obj.p (J : GrothendieckTopology C)
    (F : Sheaf J (Type (max w u))) :
    ((toStack J).obj F).p = (CategoryOfElements.π F.1).leftOp := sorry

/-- The total category of the sheaf-to-stack image is the opposite category of elements of the
underlying presheaf. -/
@[simp, stacks 0430]
theorem obj.total (J : GrothendieckTopology C)
    (F : Sheaf J (Type (max w u))) :
    ((toStack J).obj F).total = F.1.Elementsᵒᵖ := sorry

/-- The underlying set-fibred map of the sheaf-to-stack functor agrees with the canonical
category-of-elements map after the object presentation equalities. -/
@[stacks 0430]
theorem map.naturality (J : GrothendieckTopology C)
    {F G : Sheaf J (Type (max w u))} (f : F ⟶ G) :
    StackOver.Sets.Hom.toSetsMor ((toStack J).map f) ≫
        eqToHom (obj.toSets J G) =
      eqToHom (obj.toSets J F) ≫
        (FiberedCategoryOver.Sets.ofPresheaf C).map f.hom := sorry

/-- The total functor underlying the sheaf-to-stack action on a sheaf morphism is the opposite
canonical functor between categories of elements. -/
@[simp, stacks 0430]
theorem map.toFunctor (J : GrothendieckTopology C)
    {F G : Sheaf J (Type (max w u))} (f : F ⟶ G) :
    StackOver.Sets.Hom.toFunctor ((toStack J).map f) =
      (CategoryOfElements.map f.hom).op := sorry

end toStack

namespace toSheaf

/-- The presheaf underlying the stack-to-sheaf image is the specified straightening of the
underlying category fibred in sets. -/
@[simp, stacks 0430]
theorem obj.presheaf (J : GrothendieckTopology C)
    (X : StackOver.Sets.{u, v, max w u, v} J) :
    ((toSheaf J).obj X).1 =
      (FiberedCategoryOver.Sets.toPresheaf C).obj X.toSets := sorry

/-- The underlying presheaf map of the stack-to-sheaf functor is obtained by straightening the
underlying set-fibred morphism. -/
@[simp, stacks 0430]
theorem map.hom (J : GrothendieckTopology C)
    {X Y : StackOver.Sets.{u, v, max w u, v} J} (f : X ⟶ Y) :
    ((toSheaf J).map f).hom =
      (FiberedCategoryOver.Sets.toPresheaf C).map
        (StackOver.Sets.Hom.toSetsMor f) := sorry

end toSheaf

end sheafEquivalence

end StackOver.Sets

/- Axiom audit: all non-`Prop` fields come from the ambient discrete Grothendieck equivalence,
the generic restriction owner, and the direct/nested stack presentation equivalence. -/

end CategoryTheory
