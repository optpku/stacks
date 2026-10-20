module

public import ReasLib.RingTheory.Coherent.Basic
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

/-!
# Coherent Rings and Products of Flat Modules

@stack 05CZ

This leaf owns the product characterization of coherent commutative rings.  It also installs the
canonical flatness instance for products over a coherent ring, so downstream statements do not
need to reconstruct the result through a `List.TFAE` specialization.
-/

universe u v w

section

variable {R : Type u} [CommRing R]
variable {A : Type v} {M : A → Type w}
variable [∀ a, AddCommGroup (M a)] [∀ a, Module R (M a)]

namespace IsCoherentRing

/-- Products of flat modules over a coherent commutative ring are flat. -/
@[stacks 05CZ "product flatness over a coherent ring"]
instance piFlat [IsCoherentRing R]
    [∀ a, Module.Flat R (M a)] :
    Module.Flat R (∀ a, M a) := sorry

/-- A commutative ring is coherent exactly when every sufficiently large power of the ring is
flat. -/
theorem iff_piSelf_flat :
    IsCoherentRing R ↔ ∀ A : Type (max u v), Module.Flat R (A → R) := sorry

/-- Proposition 10.90.6, tag `05CZ`: coherence, flatness of arbitrary products of flat modules,
and flatness of arbitrary powers of the ring are equivalent. -/
@[stacks 05CZ]
theorem tfae_flat_products :
    List.TFAE
      [ IsCoherentRing R,
        ∀ (A : Type (max u v)) (M : A → Type (max u w))
          [∀ a, AddCommGroup (M a)] [∀ a, Module R (M a)],
          (∀ a, Module.Flat R (M a)) → Module.Flat R (∀ a, M a),
        ∀ A : Type (max u v), Module.Flat R (A → R) ] := sorry

end IsCoherentRing

end
