module

public import ReasLib.AlgebraicTopology.SimplicialSet.TrivialKanFibration
public import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 01AB

# Trivial Kan fibrations from augmented Cech nerves

The augmented Cech nerve of a surjection of types satisfies the boundary-inclusion right lifting
property.
-/

@[expose] public section

open CategoryTheory

universe u

namespace SSet.modelCategoryQuillen.I.rlp.augmentedCechNerve

/-- The augmentation of the Cech nerve of an epimorphism in `TypeCat` satisfies the
boundary-inclusion right lifting property. -/
@[stacks 01AB "Cech nerve augmentation of a TypeCat epimorphism"]
theorem of_epi {A B : Type u} (f : A ⟶ B) [Epi f] :
    I.rlp ((CategoryTheory.Arrow.mk f).augmentedCechNerve.hom) := sorry

/-- The augmentation of a Cech nerve of a surjective map of types is a trivial Kan fibration. -/
@[stacks 01AB "Cech nerve augmentation of a surjection is a trivial Kan fibration"]
theorem of_surjective {A B : Type u} (f : A → B)
    (hf : Function.Surjective f) :
    I.rlp ((CategoryTheory.Arrow.mk (TypeCat.ofHom f)).augmentedCechNerve.hom) := sorry

end SSet.modelCategoryQuillen.I.rlp.augmentedCechNerve
