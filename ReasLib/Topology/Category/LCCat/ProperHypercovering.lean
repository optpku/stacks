module

public import Mathlib.Topology.Maps.Proper.Basic
public import ReasLib.Topology.Category.LCCat.Limits
public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.Over
public import ReasLib.CategoryTheory.MorphismProperty.Hypercovering

/-!
# Proper hypercoverings of Hausdorff locally compact spaces

An augmented simplicial space is a proper hypercovering when its degree-zero
augmentation and every relative matching map are proper and surjective.
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped Simplicial

noncomputable section

namespace LCCat

/-- The morphism property of proper surjective maps of Hausdorff locally compact spaces. -/
abbrev properSurjective : MorphismProperty LCCat.{u} :=
  fun _ _ f ↦ IsProperMap f.hom ∧ Function.Surjective f.hom

/-- An augmentation is a proper hypercovering when its degree-zero augmentation and
all relative matching maps in the slice over its target are proper and surjective. -/
abbrev IsProperHypercovering {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
    (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X) : Prop :=
  MorphismProperty.Hypercovering properSurjective
    (SimplicialObject.Augmentation.toAugmented a).toOver

/-- Proper hypercoverings are characterized by proper surjectivity in degree zero
and at every relative matching map. -/
theorem isProperHypercovering_iff {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
    (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X) :
    IsProperHypercovering a ↔
      properSurjective
          (((SimplicialObject.Augmentation.toAugmented a).toOver.obj (op ⦋0⦌)).hom) ∧
        ∀ n : ℕ,
          properSurjective
            ((SimplicialObject.matchingMap
              (SimplicialObject.Augmentation.toAugmented a).toOver n).left) :=
  MorphismProperty.Hypercovering.iff_zero_matching
    (SimplicialObject.Augmentation.toAugmented a).toOver

end LCCat

end
