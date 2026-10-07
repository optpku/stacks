module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tor independence

@stack 0660

The canonical surface for Tor independence is a proposition on two bundled modules.  Keeping the
pair in `ModuleCat` makes the definition independent of a particular choice of algebra carriers and
lets the same API be used for arbitrary module objects, while algebra-specific chapter entries can
specialize with `ModuleCat.of`.  Mathlib's monoidal structure is currently available here for
`ModuleCat.{u} R` with `R : Type u`; a genuinely larger module universe should be transported by a
separate `ULift` bridge rather than by competing ambient instances.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.ModuleCat.Tor

variable {R : Type u} [CommRing R]

/-- The degree-`p` object `CategoryTheory.Tor (ModuleCat R) p` on bundled modules. -/
@[stacks 0660 "the bundled Tor object used for independence"]
noncomputable abbrev obj (p : ℕ) (M N : ModuleCat.{u} R) : ModuleCat.{u} R :=
  ((CategoryTheory.Tor (ModuleCat.{u} R) p).obj M).obj N

/-- Two bundled modules are Tor independent when all positive Tor objects vanish. -/
@[stacks 0660 "Tor independence of bundled modules"]
def IsIndependent (M N : ModuleCat.{u} R) : Prop :=
  ∀ p : ℕ, 0 < p → IsZero (obj p M N)

namespace IsIndependent

/-- Positive Tor vanishing is available at each specified degree. -/
@[stacks 0660 "positive Tor vanishing"]
theorem isZero {M N : ModuleCat.{u} R} (h : IsIndependent M N)
    {p : ℕ} (hp : 0 < p) : IsZero (obj p M N) := sorry
/- Proof strategy: unfold `IsIndependent` and apply the defining vanishing clause. -/

/-- Vanishing in every positive degree can equivalently be indexed by successors. -/
@[stacks 0660 "successor-indexed Tor independence"]
theorem iff_succ {M N : ModuleCat.{u} R} :
    IsIndependent M N ↔ ∀ n : ℕ, IsZero (obj (n + 1) M N) := sorry
/- Proof strategy: convert positive natural numbers to successor form and reuse `isZero`. -/

end IsIndependent

end CategoryTheory.ModuleCat.Tor
