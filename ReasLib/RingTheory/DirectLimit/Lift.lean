module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bijectivity criteria for maps out of ring direct limits

Mathlib supplies injectivity of a direct-limit lift from injectivity at every
stage.  This leaf adds the independent joint-surjectivity criterion and the
combined bijectivity interface.

@stack 00QT
-/

@[expose] public section

universe u v w

namespace Ring.DirectLimit

namespace Lift

variable {I : Type u} [Preorder I]
variable {R : I → Type v} [∀ i, CommRing (R i)]
variable (rho : ∀ i j, i ≤ j → R i →+* R j)
variable {T : Type w} [CommRing T]

/-- A compatible family induces a surjective map from the ring direct limit
when its stage maps jointly cover the target. -/
@[stacks 00QT "direct-limit lift cover criterion"]
theorem surjective_of_cover
    (g : ∀ i, R i →+* T)
    (hcompat : ∀ i j h x, g j (rho i j h x) = g i x)
    (hcover : ∀ x : T, ∃ (i : I) (y : R i), g i y = x) :
    Function.Surjective (Ring.DirectLimit.lift R (fun i j h ↦ rho i j h) T g hcompat) := sorry

/-- A compatible family presented by bundled ring-hom squares induces a
surjective direct-limit lift when its stage maps jointly cover the target. -/
@[stacks 00QT "direct-limit lift cover criterion"]
theorem surjective_of_comp
    (g : ∀ i, R i →+* T)
    (hcompat : ∀ i j (h : i ≤ j),
      (g j).comp (rho i j h) = g i)
    (hcover : ∀ x : T, ∃ (i : I) (y : R i), g i y = x) :
    Function.Surjective
      (Ring.DirectLimit.lift R (fun i j h ↦ rho i j h) T g
        (fun i j h x ↦ DFunLike.congr_fun (hcompat i j h) x)) := sorry

/-- A compatible family induces a bijective map from a directed ring direct
limit when every stage map is injective and the family jointly covers the
target. -/
@[stacks 00QT "direct-limit lift cover criterion"]
theorem bijective_of_injective
    [Nonempty I] [IsDirectedOrder I]
    (g : ∀ i, R i →+* T)
    (hcompat : ∀ i j h x, g j (rho i j h x) = g i x)
    (hinjective : ∀ i, Function.Injective (g i))
    (hcover : ∀ x : T, ∃ (i : I) (y : R i), g i y = x) :
    Function.Bijective (Ring.DirectLimit.lift R (fun i j h ↦ rho i j h) T g hcompat) := sorry

/-- A compatible family presented by bundled ring-hom squares induces a
bijective direct-limit lift from stagewise injections and joint coverage. -/
@[stacks 00QT "direct-limit lift cover criterion"]
theorem bijective_of_comp
    [Nonempty I] [IsDirectedOrder I]
    (g : ∀ i, R i →+* T)
    (hcompat : ∀ i j (h : i ≤ j),
      (g j).comp (rho i j h) = g i)
    (hinjective : ∀ i, Function.Injective (g i))
    (hcover : ∀ x : T, ∃ (i : I) (y : R i), g i y = x) :
    Function.Bijective
      (Ring.DirectLimit.lift R (fun i j h ↦ rho i j h) T g
        (fun i j h x ↦ DFunLike.congr_fun (hcompat i j h) x)) := sorry

end Lift

end Ring.DirectLimit
