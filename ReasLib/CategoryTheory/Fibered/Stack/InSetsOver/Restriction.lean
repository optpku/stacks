module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Restriction
public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver
import Mathlib.Tactic.CrossRefAttribute

/-!
# The ordinary full-subbicategory presentation of stacks in sets

A stack in sets can be viewed either through the established nested stack hierarchy or directly
as a category fibred in sets satisfying the stack condition.  This file gives the explicit
equivalence between those presentations.  It is the target-side bridge used when an ambient
ordinary category equivalence is restricted by an object property.
-/

@[expose] public section

universe u v w uS vS

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace IsStack.OnSite.Sets

/-- The object property on categories fibred in sets selecting those that satisfy descent for
`J`. -/
@[stacks 0430 "stack-in-sets restriction object property"]
abbrev objectProperty (J : GrothendieckTopology C) :
    ObjectProperty (FiberedCategoryOver.Sets.{u, v, uS, vS} C) :=
  fun X ↦ IsStack.OnSite J X.p

/-- The stack property on categories fibred in sets is invariant under ordinary isomorphisms. -/
@[stacks 0430 "stack-in-sets restriction isomorphism closure"]
instance objectProperty.isClosedUnderIsomorphisms (J : GrothendieckTopology C) :
    (objectProperty.{u, v, uS, vS} J).IsClosedUnderIsomorphisms := sorry

end IsStack.OnSite.Sets

namespace StackOver.Sets.Restrict

variable {J : GrothendieckTopology C}

/-- Package a category fibred in sets satisfying descent as an object of the established nested
stack-in-sets owner.  Every non-`Prop` field is inherited from the original based category. -/
@[stacks 0430 "stack-in-sets direct-to-nested object"]
noncomputable def toStackObj
    (X : (IsStack.OnSite.Sets.objectProperty J).FullSubbicategory) :
    StackOver.Sets.{u, v, max w u, v} J :=
  StackOver.Sets.mk X.1 X.property

/-- The underlying category fibred in sets of `toStackObj X` is the original object. -/
@[simp, stacks 0430 "stack-in-sets direct-to-nested object readout"]
theorem toStackObj_toSets
    (X : (IsStack.OnSite.Sets.objectProperty J).FullSubbicategory) :
    (toStackObj X).toSets = X.1 := sorry

/-- Lift a morphism between direct stack objects to the nested stack-in-sets owner. -/
@[stacks 0430 "stack-in-sets direct-to-nested morphism"]
noncomputable def toStackMap
    {X Y : (IsStack.OnSite.Sets.objectProperty J).FullSubbicategory}
    (f : X ⟶ Y) : toStackObj X ⟶ toStackObj Y :=
  StackOver.Sets.Hom.ofSetsMor f.hom

/-- The direct-to-nested morphism map preserves identities. -/
@[stacks 0430 "stack-in-sets direct-to-nested identity"]
theorem toStackMap_id
    (X : (IsStack.OnSite.Sets.objectProperty J).FullSubbicategory) :
    toStackMap (𝟙 X) = 𝟙 (toStackObj X) := sorry

/-- The direct-to-nested morphism map preserves composition. -/
@[stacks 0430 "stack-in-sets direct-to-nested composition"]
theorem toStackMap_comp
    {X Y Z : (IsStack.OnSite.Sets.objectProperty J).FullSubbicategory}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    toStackMap (f ≫ g) = toStackMap f ≫ toStackMap g := sorry

/-- Functor from the direct full-subbicategory presentation to the established stack-in-sets
owner. -/
@[stacks 0430 "stack-in-sets direct-to-nested functor"]
noncomputable def toStack :
    (IsStack.OnSite.Sets.objectProperty J).FullSubbicategory ⥤
      StackOver.Sets.{u, v, max w u, v} J where
  obj := toStackObj
  map := toStackMap
  map_id := toStackMap_id
  map_comp := toStackMap_comp

/-- The underlying category fibred in sets of a stack in sets satisfies the stack condition. -/
@[stacks 0430 "stack-in-sets nested-to-direct membership"]
theorem fromStackObj_mem (X : StackOver.Sets.{u, v, max w u, v} J) :
    IsStack.OnSite.Sets.objectProperty J X.toSets := sorry

/-- View a nested stack in sets as a directly selected category fibred in sets. -/
@[stacks 0430 "stack-in-sets nested-to-direct object"]
def fromStackObj (X : StackOver.Sets.{u, v, max w u, v} J) :
    (IsStack.OnSite.Sets.objectProperty J).FullSubbicategory :=
  ObjectProperty.FullSubbicategory.mk _ X.toSets (fromStackObj_mem X)

/-- Forget a nested stack morphism to the direct full-subbicategory presentation. -/
@[stacks 0430 "stack-in-sets nested-to-direct morphism"]
def fromStackMap {X Y : StackOver.Sets.{u, v, max w u, v} J} (f : X ⟶ Y) :
    fromStackObj X ⟶ fromStackObj Y :=
  ObjectProperty.FullSubbicategory.homMk (StackOver.Sets.Hom.toSetsMor f)

/-- The nested-to-direct morphism map preserves identities. -/
@[stacks 0430 "stack-in-sets nested-to-direct identity"]
theorem fromStackMap_id (X : StackOver.Sets.{u, v, max w u, v} J) :
    fromStackMap (𝟙 X) = 𝟙 (fromStackObj X) := sorry

/-- The nested-to-direct morphism map preserves composition. -/
@[stacks 0430 "stack-in-sets nested-to-direct composition"]
theorem fromStackMap_comp {X Y Z : StackOver.Sets.{u, v, max w u, v} J}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    fromStackMap (f ≫ g) = fromStackMap f ≫ fromStackMap g := sorry

/-- Functor from the established stack-in-sets owner to its direct full-subbicategory
presentation. -/
@[stacks 0430 "stack-in-sets nested-to-direct functor"]
def fromStack :
    StackOver.Sets.{u, v, max w u, v} J ⥤
      (IsStack.OnSite.Sets.objectProperty J).FullSubbicategory where
  obj := fromStackObj
  map := fromStackMap
  map_id := fromStackMap_id
  map_comp := fromStackMap_comp

/-- The direct-side comparison is the explicit identity-owner isomorphism for the unchanged
underlying set-fibred category. -/
@[stacks 0430 "stack-in-sets restriction unit component"]
noncomputable def unitApp
    (X : (IsStack.OnSite.Sets.objectProperty J).FullSubbicategory) :
    X ≅ (toStack ⋙ fromStack).obj X :=
  ObjectProperty.FullSubbicategory.isoMk
    (StackOver.Sets.mk.toSetsIso X.1 X.property).symm

/-- Naturality of the direct-side comparison. -/
@[stacks 0430 "stack-in-sets restriction unit naturality"]
theorem unitApp_naturality
    {X Y : (IsStack.OnSite.Sets.objectProperty J).FullSubbicategory}
    (f : X ⟶ Y) :
    f ≫ (unitApp Y).hom = (unitApp X).hom ≫ (toStack ⋙ fromStack).map f := sorry

/-- Unit isomorphism comparing the direct presentation with its round trip through the nested
owner. -/
@[stacks 0430 "stack-in-sets restriction unit"]
noncomputable def unitIso :
    Functor.id (IsStack.OnSite.Sets.objectProperty J).FullSubbicategory ≅
      toStack (J := J) ⋙ fromStack (J := J) :=
  NatIso.ofComponents unitApp (fun _ ↦ unitApp_naturality _)

/-- The explicit set-fibred owner isomorphism underlying the nested-side comparison. -/
@[stacks 0430 "stack-in-sets restriction counit owner"]
noncomputable def counitSetsIso (X : StackOver.Sets.{u, v, max w u, v} J) :
    ((fromStack ⋙ toStack).obj X).toSets ≅ X.toSets :=
  StackOver.Sets.mk.toSetsIso X.toSets (fromStackObj_mem X)

/-- The nested-side comparison is the lift of its explicit set-fibred identity transport. -/
@[stacks 0430 "stack-in-sets restriction counit component"]
noncomputable def counitApp (X : StackOver.Sets.{u, v, max w u, v} J) :
    (fromStack ⋙ toStack).obj X ≅ X :=
  StackOver.Sets.isoOfSets (counitSetsIso X)

/-- Naturality of the nested-side comparison. -/
@[stacks 0430 "stack-in-sets restriction counit naturality"]
theorem counitApp_naturality {X Y : StackOver.Sets.{u, v, max w u, v} J}
    (f : X ⟶ Y) :
    (fromStack ⋙ toStack).map f ≫ (counitApp Y).hom =
      (counitApp X).hom ≫ f := sorry

/-- Counit isomorphism comparing the nested stack-in-sets owner with its direct round trip. -/
@[stacks 0430 "stack-in-sets restriction counit"]
noncomputable def counitIso :
    fromStack (J := J) ⋙ toStack (J := J) ≅
      Functor.id (StackOver.Sets.{u, v, max w u, v} J) :=
  NatIso.ofComponents counitApp (fun _ ↦ counitApp_naturality _)

/-- The direct-to-nested functor and its comparison isomorphisms satisfy the triangle identity. -/
@[stacks 0430 "stack-in-sets restriction triangle"]
theorem functor_unitIso_comp
    (X : (IsStack.OnSite.Sets.objectProperty J).FullSubbicategory) :
    toStack.map (unitIso.hom.app X) ≫ counitIso.hom.app (toStack.obj X) = 𝟙 _ := sorry

/-- The direct full-subbicategory presentation of stacks in sets is equivalent to the established
nested owner.  Both functors and both comparison isomorphisms are explicit. -/
@[stacks 0430 "stack-in-sets restriction equivalence"]
noncomputable def equivalence :
    (IsStack.OnSite.Sets.objectProperty J).FullSubbicategory ≌
      StackOver.Sets.{u, v, max w u, v} J where
  functor := toStack
  inverse := fromStack
  unitIso := unitIso
  counitIso := counitIso
  functor_unitIso_comp := functor_unitIso_comp

end StackOver.Sets.Restrict

end CategoryTheory
