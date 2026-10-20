module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Composition.Restriction

/-!
# Open restriction of composition of families of cycles on fibres

This file records that forming the composite family `α ∘ β` commutes with
restriction to compatible opens of the source and of the intermediate scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

/- Lemma 62.13.2: If `U ⊂ X` and `V ⊂ Y` are open and `f(U) ⊂ V`, then
`(α ∘ β)|_U` is equal to `α|_U ∘ β|_V`. -/
@[stacks 0H6J] #check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.comp_restrict :
  ∀ {S X Y : Scheme.{u}} (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] {r e : ℕ}
    (α : CyclesOnFibers f (r : ℤ)) (β : CyclesOnFibers p (e : ℤ)) (U : X.Opens)
    (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V) (s : S)
    (x : (U.ι ≫ f ≫ p).fiber s),
    toAlgebraicCycle (restrictOver (comp α β) U) s x =
      toAlgebraicCycle
        (comp (restrict α U V hUV) (restrictOver β V))
        s (compRestrictFiberMap p f U V hUV s x))

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
