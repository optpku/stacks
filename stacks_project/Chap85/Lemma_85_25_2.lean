module

public import ReasLib.Topology.Sheaves.Simplicial.ProperDescent
import StacksCheckRecall

/-!
# Lemma 85.25.2

Along a proper hypercovering, augmentation inverse image on sheaves of sets and
abelian sheaves is fully faithful with precisely cartesian essential image and
quasi-inverse given by augmentation direct image.
-/

@[expose] public section

universe u

open CategoryTheory
open CategoryTheory.SimplicialObject

variable {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
variable (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X)

/- Lemma 85.25.2 (1). Proper hypercovering descent for sheaves of sets, with
augmentation inverse image and direct image as the forward and inverse functors. -/
@[stacks 0DAG] #check (LCCat.sheafCartesianEquivalence a :
  LCCat.IsProperHypercovering a →
    (Sheaf (Opens.grothendieckTopology X.obj) (Type u) ≌
      Cartesian (LCCat.forgetToTop.obj U) (Type u)))

/- Lemma 85.25.2 (2). Proper hypercovering descent for abelian sheaves, with
augmentation inverse image and direct image as the forward and inverse functors. -/
@[stacks 0DAG] #check (LCCat.abelianCartesianEquivalence a :
  LCCat.IsProperHypercovering a →
    (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u} ≌
      Cartesian (LCCat.forgetToTop.obj U) AddCommGrpCat.{u}))
