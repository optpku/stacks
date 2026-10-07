module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.Forgetful
public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver
import Mathlib.Tactic.CrossRefAttribute

/-!
# Forgetting stacks in sets to set-fibred categories

The canonical forgetful operation is packaged here as a strict pseudofunctor, including its
`2`-cell action. It reuses the stack-in-setoids forgetful pseudofunctor and the generic lift to
the full subbicategory selected by discrete fibrations.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Sets

variable {J : GrothendieckTopology C}

namespace toSets

/-- The ambient based-category action underlying the forgetful strict pseudofunctor from
stacks in sets. -/
private def ambient (J : GrothendieckTopology C) :
    StrictPseudofunctor (StackOver.Sets.{u, v} J) (BasedCategory C) :=
  (StackOver.Sets.forget J).comp
    ((StackOver.Setoids.toSetoids.pseudofunctor J).comp
      (FiberedCategoryOver.Setoids.toBased C))

/-- Every object in the ambient image retains the discrete-fibration property of the source
stack. -/
private theorem ambient_obj_mem (J : GrothendieckTopology C)
    (X : StackOver.Sets.{u, v} J) :
    BasedCategory.isFiberedInSets C ((ambient J).obj X) := sorry

/-- The canonical strict pseudofunctor forgetting a stack in sets to its underlying
set-fibred category. -/
@[stacks 02ZK "set-stack forgetful pseudofunctor"]
def pseudofunctor (J : GrothendieckTopology C) :
    StrictPseudofunctor (StackOver.Sets.{u, v} J)
      (FiberedCategoryOver.Sets C) :=
  ObjectProperty.FullSubbicategory.lift (ambient J) (ambient_obj_mem J)

/-- The object action of the forgetful strict pseudofunctor is the canonical set-fibred
view. -/
@[simp, stacks 02ZK "set-stack forgetful object readout"]
theorem pseudofunctor.obj (J : GrothendieckTopology C)
    (X : StackOver.Sets.{u, v} J) :
    (pseudofunctor J).obj X = X.toSets := sorry

/-- The underlying based category of the object image is the original stack's based category. -/
@[simp, stacks 02ZK "set-stack forgetful based-category readout"]
theorem pseudofunctor.obj.toBasedCategory (J : GrothendieckTopology C)
    (X : StackOver.Sets.{u, v} J) :
    ((pseudofunctor J).obj X).toBasedCategory = X.toBasedCategory := sorry

/-- The total category of the object image is the original stack's total category. -/
@[simp, stacks 02ZK "set-stack forgetful total-category readout"]
theorem pseudofunctor.obj.total (J : GrothendieckTopology C)
    (X : StackOver.Sets.{u, v} J) :
    ((pseudofunctor J).obj X).total = X.total := sorry

/-- The projection of the object image is the original stack projection. -/
@[simp, stacks 02ZK "set-stack forgetful projection readout"]
theorem pseudofunctor.obj.p (J : GrothendieckTopology C)
    (X : StackOver.Sets.{u, v} J) :
    ((pseudofunctor J).obj X).p = X.p := sorry

/-- The ambient based functor of a mapped `1`-cell is the based-functor view of
`Hom.toSetsMor`. This projection avoids exposing transports between proof-bearing full
subbicategory objects. -/
@[simp, stacks 02ZK "set-stack forgetful morphism readout"]
theorem pseudofunctor.map.hom (J : GrothendieckTopology C)
    {X Y : StackOver.Sets.{u, v} J} (F : X ⟶ Y) :
    ((pseudofunctor J).map F).hom =
      FiberedCategoryOver.Sets.toBasedFunctor (Hom.toSetsMor F) := sorry

/-- The based functor underlying the mapped `1`-cell is the canonical stack-morphism
projection. -/
@[simp, stacks 02ZK "set-stack forgetful based-functor readout"]
theorem pseudofunctor.map.toBasedFunctor (J : GrothendieckTopology C)
    {X Y : StackOver.Sets.{u, v} J} (F : X ⟶ Y) :
    FiberedCategoryOver.Sets.toBasedFunctor ((pseudofunctor J).map F) =
      Hom.toBasedFunctor F := sorry

/-- The total functor underlying the mapped `1`-cell is the canonical stack-morphism
projection. -/
@[simp, stacks 02ZK "set-stack forgetful total-functor readout"]
theorem pseudofunctor.map.toFunctor (J : GrothendieckTopology C)
    {X Y : StackOver.Sets.{u, v} J} (F : X ⟶ Y) :
    FiberedCategoryOver.Sets.toFunctor ((pseudofunctor J).map F) =
      Hom.toFunctor F := sorry

/-- The fiber functor underlying the mapped `1`-cell is the canonical stack-morphism fiber
action. -/
@[simp, stacks 02ZK "set-stack forgetful fiber-functor readout"]
theorem pseudofunctor.map.fiberFunctor (J : GrothendieckTopology C)
    {X Y : StackOver.Sets.{u, v} J} (F : X ⟶ Y) (U : C) :
    FiberedCategoryOver.Sets.fiberFunctor ((pseudofunctor J).map F) U =
      Hom.fiberFunctor F U := sorry

/-- On each hom category, the forgetful strict pseudofunctor sends objects by
`Hom.toSetsMor`. -/
@[simp, stacks 02ZK "set-stack forgetful Hom object readout"]
theorem pseudofunctor.mapFunctor.obj.hom (J : GrothendieckTopology C)
    {X Y : StackOver.Sets.{u, v} J} (F : X ⟶ Y) :
    (((pseudofunctor J).mapFunctor X Y).obj F).hom =
      FiberedCategoryOver.Sets.toBasedFunctor (Hom.toSetsMor F) := sorry

/-- The ordinary functor previously exposed for `1`-categorical consumers is the underlying
functor of the strict pseudofunctor. -/
@[stacks 02ZK "set-stack forgetful ordinary functor bridge"]
theorem pseudofunctor.toFunctor (J : GrothendieckTopology C) :
    (pseudofunctor J).toFunctor = toSets.functor J := sorry

end toSets

namespace Hom₂

variable {X Y : StackOver.Sets J} {F G : X ⟶ Y}

/-- Forget a `2`-morphism of stacks in sets to the corresponding `2`-morphism produced by the
canonical set-fibred forgetful pseudofunctor. -/
@[stacks 02ZK "set-stack forgetful 2-cell"]
def toSetsNatTrans (eta : F ⟶ G) :
    (toSets.pseudofunctor J).map F ⟶
      (toSets.pseudofunctor J).map G :=
  (toSets.pseudofunctor J).map₂ eta

/-- The based natural transformation underlying the set-fibred image of a stack
`2`-morphism. -/
@[stacks 02ZK "set-stack forgetful based natural transformation"]
def toBasedNatTrans (eta : F ⟶ G) :=
  (toSetsNatTrans eta).hom

/-- The ordinary natural transformation on total categories underlying the set-fibred image of
a stack `2`-morphism. -/
@[stacks 02ZK "set-stack forgetful total natural transformation"]
def toNatTrans (eta : F ⟶ G) :=
  (toBasedNatTrans eta).toNatTrans

/-- Forgetting an identity `2`-morphism and then projecting to based natural transformations
gives the identity projection. -/
@[simp, stacks 02ZK "set-stack forgetful based natural identity"]
theorem toBasedNatTrans.id (F : X ⟶ Y) :
    toBasedNatTrans (𝟙 F) =
      𝟙 ((toSets.pseudofunctor J).map F).hom := sorry

/-- Projection to based natural transformations preserves vertical composition. -/
@[simp, stacks 02ZK "set-stack forgetful based natural composition"]
theorem toBasedNatTrans.comp {H : X ⟶ Y}
    (eta : F ⟶ G) (theta : G ⟶ H) :
    toBasedNatTrans (eta ≫ theta) =
      toBasedNatTrans eta ≫ toBasedNatTrans theta := sorry

/-- Forgetting an identity `2`-morphism and then projecting to total categories gives the
identity natural transformation. -/
@[simp, stacks 02ZK "set-stack forgetful total natural identity"]
theorem toNatTrans.id (F : X ⟶ Y) :
    toNatTrans (𝟙 F) =
      𝟙 ((toSets.pseudofunctor J).map F).hom.toFunctor := sorry

/-- Projection to total-category natural transformations preserves vertical composition. -/
@[simp, stacks 02ZK "set-stack forgetful total natural composition"]
theorem toNatTrans.comp {H : X ⟶ Y}
    (eta : F ⟶ G) (theta : G ⟶ H) :
    toNatTrans (eta ≫ theta) =
      NatTrans.vcomp (toNatTrans eta) (toNatTrans theta) := sorry

/-- Forgetting the identity `2`-morphism gives the identity on the mapped set-fibred
`1`-morphism. -/
@[simp, stacks 02ZK "set-stack forgetful 2-cell identity"]
theorem toSetsNatTrans.id (F : X ⟶ Y) :
    toSetsNatTrans (𝟙 F) =
      𝟙 ((toSets.pseudofunctor J).map F) := sorry

/-- Forgetting a vertical composite preserves its order and composition. -/
@[simp, stacks 02ZK "set-stack forgetful 2-cell composition"]
theorem toSetsNatTrans.comp {H : X ⟶ Y}
    (eta : F ⟶ G) (theta : G ⟶ H) :
    toSetsNatTrans (eta ≫ theta) =
      toSetsNatTrans eta ≫ toSetsNatTrans theta := sorry

end Hom₂

namespace toSets

/-- The `2`-cell action of the forgetful strict pseudofunctor is the named direct projection
`Hom₂.toSetsNatTrans`. -/
@[simp, stacks 02ZK "set-stack forgetful pseudofunctor 2-cell readout"]
theorem pseudofunctor.map₂ (J : GrothendieckTopology C)
    {X Y : StackOver.Sets.{u, v} J} {F G : X ⟶ Y} (eta : F ⟶ G) :
    (pseudofunctor J).map₂ eta = Hom₂.toSetsNatTrans eta := sorry

/-- The based natural transformation underlying the mapped `2`-cell is the named direct
projection. -/
@[simp, stacks 02ZK "set-stack forgetful 2-cell based readout"]
theorem pseudofunctor.map₂.hom (J : GrothendieckTopology C)
    {X Y : StackOver.Sets.{u, v} J} {F G : X ⟶ Y} (eta : F ⟶ G) :
    ((pseudofunctor J).map₂ eta).hom = Hom₂.toBasedNatTrans eta := sorry

/-- The total natural transformation underlying the mapped `2`-cell is the named direct
projection. -/
@[simp, stacks 02ZK "set-stack forgetful 2-cell total readout"]
theorem pseudofunctor.map₂.toNatTrans (J : GrothendieckTopology C)
    {X Y : StackOver.Sets.{u, v} J} {F G : X ⟶ Y} (eta : F ⟶ G) :
    ((pseudofunctor J).map₂ eta).hom.toNatTrans = Hom₂.toNatTrans eta := sorry

/-- Restricting the mapped `2`-cell to a fiber agrees with restricting its named based
projection. -/
@[simp, stacks 02ZK "set-stack forgetful 2-cell fiber readout"]
theorem pseudofunctor.map₂.fiber (J : GrothendieckTopology C)
    {X Y : StackOver.Sets.{u, v} J} {F G : X ⟶ Y}
    (eta : F ⟶ G) (U : C) :
    BasedNatTrans.fiber ((pseudofunctor J).map₂ eta).hom U =
      BasedNatTrans.fiber (Hom₂.toBasedNatTrans eta) U := sorry

/-- On each hom category, the ambient based natural transformation of a mapped `2`-cell is the
ambient projection of `Hom₂.toSetsNatTrans`. -/
@[simp, stacks 02ZK "set-stack forgetful Hom morphism readout"]
theorem pseudofunctor.mapFunctor.map.hom (J : GrothendieckTopology C)
    {X Y : StackOver.Sets.{u, v} J} {F G : X ⟶ Y} (eta : F ⟶ G) :
    (((pseudofunctor J).mapFunctor X Y).map eta).hom =
      Hom₂.toBasedNatTrans eta := sorry

end toSets

end StackOver.Sets

end CategoryTheory
