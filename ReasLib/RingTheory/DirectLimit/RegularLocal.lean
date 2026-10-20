module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.RingTheory.DirectLimit.Local
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Regular local rings and directed colimits

@stack 07DX

This leaf records the regular-local consequence of the canonical local-ring
structure on a directed colimit.
-/

universe u v

namespace Ring.DirectLimit

/-- Lemma 10.106.8 (07DX): a directed colimit of regular local rings along
local homomorphisms is regular local whenever the colimit is Noetherian. -/
@[stacks 07DX]
theorem isRegularLocalRing
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (R : I → Type u) [∀ i, CommRing (R i)]
    (φ : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ φ i j h)]
    [∀ i, IsRegularLocalRing (R i)] [∀ i j h, IsLocalHom (φ i j h)]
    (hNoetherian : IsNoetherianRing (Ring.DirectLimit R (fun i j h ↦ φ i j h))) :
    IsRegularLocalRing (Ring.DirectLimit R (fun i j h ↦ φ i j h)) := sorry

end Ring.DirectLimit
