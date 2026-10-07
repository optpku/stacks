module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Gabriel-Popescu functors for Grothendieck abelian categories

This file exposes the exactness and adjunction API for the canonical Gabriel-Popescu
functors. Results for an arbitrary separator retain the separator hypothesis explicitly;
the distinguished object `separator C` receives reusable global instances.
-/

open CategoryTheory Limits

universe v u

namespace CategoryTheory.IsGrothendieckAbelian.GabrielPopescu

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]

/-- Lemma 19.14.2: the adjoint transpose of a monomorphism into the
Gabriel-Popescu embedding is a monomorphism. -/
@[stacks 0F5T]
theorem adjointMap_mono {U A : C} {M : ModuleCat (End U)ᵐᵒᵖ}
    (hU : IsSeparator U) {f : M ⟶ (preadditiveCoyonedaObj U).obj A}
    [Mono f] :
    Mono (((tensorObjPreadditiveCoyonedaObjAdjunction U).homEquiv M A).symm f) := sorry

/-- Explicit-proof bridge for `adjointMap_mono`; the canonical API obtains monicity of `f` by
typeclass search. -/
@[stacks 0F5T "explicit monomorphism bridge"]
theorem adjointMap_mono_of {U A : C} {M : ModuleCat (End U)ᵐᵒᵖ}
    (hU : IsSeparator U) {f : M ⟶ (preadditiveCoyonedaObj U).obj A}
    (hf : Mono f) :
    Mono (((tensorObjPreadditiveCoyonedaObjAdjunction U).homEquiv M A).symm f) := sorry

/-- Theorem 19.14.3: the Gabriel-Popescu left adjoint attached to a separator is exact. -/
@[stacks 0F5U "exact left adjoint"]
theorem tensorExact (U : C) (hU : IsSeparator U) :
    exactFunctor _ _ (tensorObj U) := sorry

/-- The canonical Gabriel-Popescu left adjoint preserves finite limits. -/
@[stacks 0F5U "canonical left exactness"]
instance tensorSeparatorPreservesFiniteLimits :
    PreservesFiniteLimits (tensorObj (separator C)) := sorry

/-- The canonical Gabriel-Popescu left adjoint preserves finite colimits. -/
@[stacks 0F5U "canonical right exactness"]
instance tensorSeparatorPreservesFiniteColimits :
    PreservesFiniteColimits (tensorObj (separator C)) := sorry

/-- The canonical Gabriel-Popescu left adjoint is additive. -/
@[stacks 0F5U "canonical additivity"]
instance tensorSeparatorAdditive :
    (tensorObj (separator C)).Additive := sorry

/-- The canonical Gabriel-Popescu embedding is full. -/
@[stacks 0F5U "canonical fullness"]
instance coyonedaSeparatorFull :
    (preadditiveCoyonedaObj (separator C)).Full := sorry

/-- The canonical Gabriel-Popescu embedding is faithful. -/
@[stacks 0F5U "canonical faithfulness"]
instance coyonedaSeparatorFaithful :
    (preadditiveCoyonedaObj (separator C)).Faithful := sorry

/-- The counit of the canonical Gabriel-Popescu adjunction is invertible. -/
@[stacks 0F5U "canonical counit"]
instance counitIsIso :
    IsIso (tensorObjPreadditiveCoyonedaObjAdjunction (separator C)).counit := sorry

end CategoryTheory.IsGrothendieckAbelian.GabrielPopescu
