module

public import ReasLib.CategoryTheory.InverseSystem.Milnor.Derived.Canonical
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Additivity of the canonical first derived limit

@stack 08TC

The canonical Milnor cokernel construction is additive in morphisms of sequential inverse
systems. This leaf records the map computation and installs the corresponding functor instance.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.SequentialInverseSystem.Milnor.ProductCone.canonicalR1

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCokernels C] [HasCountableProducts C]

/-- The canonical first-derived-limit map preserves addition of morphisms of sequential
inverse systems. -/
@[simp, stacks 08TC]
theorem map_add {K L : SequentialInverseSystem C} (f g : K ⟶ L) :
    map (f + g) = map f + map g := sorry

/-- The canonical first-derived-limit functor is additive. -/
@[stacks 08TC]
instance functorAdditive : (functor (C := C)).Additive := sorry

#synth (functor (C := C)).Additive

end CategoryTheory.SequentialInverseSystem.Milnor.ProductCone.canonicalR1

end
