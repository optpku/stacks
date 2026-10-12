/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.OfPresheaf
public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver
import Mathlib.Tactic.CrossRefAttribute

/-!
# The category-of-elements functor on sheaves

This leaf packages the arbitrary-universe forward construction from set-valued sheaves to
stacks in sets. The category of elements and its action on morphisms remain owned by
`FiberedCategoryOver.Sets.ofPresheaf`; this file only supplies the site-dependent stack witness.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace CategoryOfElements

/-- A set-valued presheaf is a sheaf for `J` exactly when its opposite category-of-elements
projection is a stack in sets over `(C, J)`. -/
@[stacks 0430]
theorem isSheaf_iff_stackInSets
    (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsSheaf J F ↔ IsStack.InSets J ((π F).leftOp) := sorry

/-- The category-of-elements sheaf criterion using the underlying stack-on-site predicate. -/
@[stacks 0430 "category-of-elements stack-on-site criterion"]
theorem isSheaf_iff_stackOnSite
    (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsSheaf J F ↔ IsStack.OnSite J ((π F).leftOp) := sorry

end CategoryOfElements

namespace StackOver.Sets

namespace OfSheaf

/-- The opposite category-of-elements projection of a sheaf is a stack in sets. -/
@[stacks 0430 "category-of-elements projection stack closure"]
theorem projectionIsStack
    (J : GrothendieckTopology C) (F : Sheaf J (Type w)) :
    IsStack.InSets J ((CategoryOfElements.π F.1).leftOp) := sorry

/-- The canonical set-fibred category of elements of a sheaf satisfies descent on the site. -/
@[stacks 0430 "category-of-elements set-fibred stack closure"]
theorem isStackOnSite
    (J : GrothendieckTopology C) (F : Sheaf J (Type w)) :
    IsStack.OnSite J ((FiberedCategoryOver.Sets.ofPresheaf C).obj F.1).p := sorry

/-- The stack in sets obtained from a sheaf by the discrete Grothendieck construction. -/
@[stacks 0430 "stack in sets associated to a sheaf"]
noncomputable def obj
    (J : GrothendieckTopology C) (F : Sheaf J (Type w)) :
    StackOver.Sets.{u, v, max u w, v} J :=
  StackOver.Sets.mk ((FiberedCategoryOver.Sets.ofPresheaf C).obj F.1)
    (isStackOnSite J F)

/-- A sheaf morphism induces the canonical morphism between its category-of-elements stacks. -/
@[stacks 0430 "category-of-elements stack morphism"]
noncomputable def map
    (J : GrothendieckTopology C) {F G : Sheaf J (Type w)} (f : F ⟶ G) :
    obj J F ⟶ obj J G :=
  StackOver.Sets.Hom.ofSetsMor
    ((FiberedCategoryOver.Sets.ofPresheaf C).map f.hom)

/-- The category-of-elements stack map preserves identity morphisms. -/
@[stacks 0430 "category-of-elements stack identity map"]
theorem map_id (J : GrothendieckTopology C) (F : Sheaf J (Type w)) :
    map J (𝟙 F) = 𝟙 (obj J F) := sorry

/-- The category-of-elements stack map preserves composition. -/
@[stacks 0430 "category-of-elements stack composition map"]
theorem map_comp
    (J : GrothendieckTopology C)
    {F G H : Sheaf J (Type w)} (f : F ⟶ G) (g : G ⟶ H) :
    map J (f ≫ g) = map J f ≫ map J g := sorry

end OfSheaf

/-- The arbitrary-universe functor sending a set-valued sheaf to its category-of-elements
stack in sets. -/
@[stacks 0430 "sheaf to category-of-elements stack"]
noncomputable def ofSheaf (J : GrothendieckTopology C) :
    Sheaf J (Type w) ⥤ StackOver.Sets.{u, v, max u w, v} J where
  obj := OfSheaf.obj J
  map := OfSheaf.map J
  map_id := OfSheaf.map_id J
  map_comp := OfSheaf.map_comp J

namespace ofSheaf

/-- Forgetting the stack witness from `ofSheaf` recovers the discrete Grothendieck
construction of the underlying presheaf. -/
@[simp, stacks 0430 "sheaf-to-stack underlying set-fibred view"]
theorem obj.toSets (J : GrothendieckTopology C) (F : Sheaf J (Type w)) :
    ((ofSheaf J).obj F).toSets =
      (FiberedCategoryOver.Sets.ofPresheaf C).obj F.1 := sorry

/-- The projection of the category-of-elements stack is the opposite elements projection. -/
@[simp, stacks 0430 "sheaf-to-stack projection readout"]
theorem obj.p (J : GrothendieckTopology C) (F : Sheaf J (Type w)) :
    ((ofSheaf J).obj F).p =
      (CategoryOfElements.π F.1).leftOp := sorry

/-- The total category of the category-of-elements stack is the opposite category of elements. -/
@[simp, stacks 0430 "sheaf-to-stack total-category readout"]
theorem obj.total (J : GrothendieckTopology C) (F : Sheaf J (Type w)) :
    ((ofSheaf J).obj F).total = F.1.Elementsᵒᵖ := sorry

/-- Forgetting a sheaf-induced stack morphism recovers the canonical set-fibred
category-of-elements morphism. -/
@[simp, stacks 0430 "sheaf-to-stack morphism set-fibred readout"]
theorem map.toSetsMor
    (J : GrothendieckTopology C)
    {F G : Sheaf J (Type w)} (f : F ⟶ G) :
    StackOver.Sets.Hom.toSetsMor ((ofSheaf J).map f) =
      (FiberedCategoryOver.Sets.ofPresheaf C).map f.hom := sorry

/-- The total functor of a sheaf-induced stack morphism is the canonical opposite
category-of-elements map. -/
@[simp, stacks 0430 "sheaf-to-stack morphism total readout"]
theorem map.toFunctor
    (J : GrothendieckTopology C)
    {F G : Sheaf J (Type w)} (f : F ⟶ G) :
    StackOver.Sets.Hom.toFunctor ((ofSheaf J).map f) =
      (CategoryOfElements.map f.hom).op := sorry

end ofSheaf

/- Data audit: object and morphism payload come directly from `ofPresheaf`,
`StackOver.Sets.mk`, and `Hom.ofSetsMor`. The new deferred fields are the stack witness and
ordinary functor laws; no category-of-elements object or map is selected again. -/

end StackOver.Sets

end CategoryTheory
