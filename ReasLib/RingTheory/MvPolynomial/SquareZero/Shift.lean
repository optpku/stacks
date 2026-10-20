module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import ReasLib.Algebra.Module.CountablyGenerated.Basic
public import ReasLib.LinearAlgebra.QuotientByIdeal
public import ReasLib.LinearAlgebra.UniversallyInjective.Projective
public import ReasLib.RingTheory.Flatness.MittagLeffler.Projective
public import ReasLib.RingTheory.Ideal.AssociatedPrime.AutoAssociated
public import ReasLib.RingTheory.MvPolynomial.SquareZero
import Mathlib.Tactic.CrossRefAttribute

/-!
# The square-zero shift counterexample

@stack 05GR

This file owns the explicit countable shift over the square-zero polynomial quotient. Its cokernel
is the standard countably generated flat module that is neither projective nor Mittag-Leffler.
-/

@[expose] public section

open IsLocalRing

universe u

namespace MvPolynomial.SquareZero.Shift

section Data

variable (k : Type u) [CommRing k]

/-- The square-zero coefficient ring in Example 15.15.5. -/
@[stacks 05GR "square-zero coefficient ring"]
abbrev Ring := MvPolynomial.SquareZero.Quotient (σ := ℕ) (k := k)

/-- The countably generated free module in Example 15.15.5. -/
@[stacks 05GR "countable free module"]
abbrev Free := ℕ →₀ Ring k

/-- The image of the `i`-th polynomial variable in the square-zero quotient. -/
@[stacks 05GR "square-zero variable"]
noncomputable abbrev generator (i : ℕ) : Ring k :=
  MvPolynomial.SquareZero.generator (σ := ℕ) (k := k) i

/-- The family `e_i - x_i e_{i+1}` defining the square-zero shift. -/
@[stacks 05GR "shift family"]
noncomputable def family (i : ℕ) : Free k :=
  Finsupp.single i 1 - Finsupp.single (i + 1) (generator k i)

/-- Example 15.15.5: the linear map `e_i ↦ e_i - x_i e_{i+1}` on the countable free module. -/
@[stacks 05GR "Example 15.15.5, shift map"]
noncomputable def map : Free k →ₗ[Ring k] Free k :=
  Finsupp.linearCombination (Ring k) (family k)

/-- The cokernel of the explicit square-zero shift. -/
@[stacks 05GR "square-zero shift cokernel"]
abbrev Cokernel := Free k ⧸ LinearMap.range (map k)

/-- The square-zero shift on a single basis term. -/
@[stacks 05GR "shift map on basis terms"]
theorem map_single (i : ℕ) (r : Ring k) :
    map k (Finsupp.single i r) =
      Finsupp.single i r - Finsupp.single (i + 1) (generator k i * r) := sorry
-- Proof strategy: unfold `map` and `family`, rewrite with
-- `Finsupp.linearCombination_single`, and check the resulting scalar multiple of the difference
-- of two singleton vectors coordinatewise.

end Data

variable (k : Type u) [Field k]

/-- Example 15.15.5 (1): the square-zero quotient with countably many variables is
auto-associated. -/
@[stacks 05GR "Example 15.15.5 (1), auto-associated square-zero quotient"]
instance ring_isAutoAssociated : IsAutoAssociatedRing (Ring k) := sorry
-- Proof strategy: use `generator k 0` as the weak-association witness.  Show that the radical of
-- its torsion ideal is `maximalIdeal (Ring k)` using the square-zero generator relations and the
-- nonvanishing of finite products of distinct generators; then rewrite
-- `isAutoAssociatedRing_iff` and identify the unique minimal prime.

/-- Example 15.15.5 (2): the square-zero shift is injective. -/
@[stacks 05GR "Example 15.15.5 (2), injective"]
theorem injective : Function.Injective (map k) := sorry
-- Proof strategy: derive the triangular coordinate formulas: coordinate zero is unchanged and
-- coordinate `n + 1` is `l (n + 1) - generator k n * l n`.  If `map k l = 0`, induct on `n` to
-- show every coefficient of the finitely supported vector `l` is zero.

/-- Example 15.15.5 (3): the square-zero shift is universally injective. -/
@[stacks 05GR "Example 15.15.5 (3), universally injective"]
theorem universallyInjective :
    LinearMap.UniversallyInjective.{u, u, u, u} (map k) := sorry
-- Proof strategy: obtain the annihilator property from the canonical
-- `ring_isAutoAssociated` instance and
-- `IsAutoAssociatedRing.annihilator_ne_bot_of_fg_of_ne_top`, then apply
-- `LinearMap.UniversallyInjective.iff_injective_of_projective_of_annihilator` to `injective k`;
-- both Finsupp modules are free and hence projective.

/-- Example 15.15.5 (4): reduction of the square-zero shift modulo the maximal ideal is
bijective. Via `MvPolynomial.SquareZero.residueFieldAlgEquiv`, this is the source map
`map k ⊗ id_k`. -/
@[stacks 05GR "Example 15.15.5 (4), residue map bijective"]
theorem quotientMapByMaximalIdeal_bijective :
    Function.Bijective ((map k).quotientMapByIdeal (maximalIdeal (Ring k))) := sorry
-- Proof strategy: `map_single` differs from the identity by a singleton whose coefficient is a
-- generator in the maximal ideal.  Extend this by Finsupp induction, show the induced quotient map
-- is `LinearMap.id` on quotient representatives, and conclude bijectivity.

/-- Example 15.15.5 (5): the square-zero shift is not surjective. -/
@[stacks 05GR "Example 15.15.5 (5), not surjective"]
theorem not_surjective : ¬ Function.Surjective (map k) := sorry
-- Proof strategy: a preimage of the zeroth basis vector would satisfy
-- `l (n + 1) = generator k n * l n`, so its coefficients are successive finite prefix products
-- of distinct generators.  These products are nonzero in the square-zero quotient, contradicting
-- finite support.

/-- Example 15.15.5 (6): the injective square-zero shift has no linear retraction. -/
@[stacks 05GR "Example 15.15.5 (6), not split"]
theorem not_split :
    ¬ ∃ r : Free k →ₗ[Ring k] Free k, r.comp (map k) = LinearMap.id := sorry
-- Proof strategy: from a hypothetical retraction, take its projective kernel complement.  The
-- quotient computations force that kernel into `maximalIdeal (Ring k) • ⊤`; projectivity over the
-- local ring makes it free, so the basis-coordinate Nakayama argument makes it subsingleton.  The
-- retraction would then make `map k` surjective, contradicting `not_surjective k`.

/-- Example 15.15.5 (7): the cokernel of the square-zero shift is flat. -/
@[stacks 05GR "Example 15.15.5 (7), flat cokernel"]
theorem cokernel_flat : Module.Flat (Ring k) (Cokernel k) := sorry
-- Proof strategy: apply the canonical cokernel-flatness criterion for a universally injective map
-- between flat modules to `universallyInjective k`; the source and target Finsupp modules are free.

/-- Example 15.15.5 (8): the cokernel of the square-zero shift is countably generated. -/
@[stacks 05GR "Example 15.15.5 (8), countably generated cokernel"]
theorem cokernel_countablyGenerated : Module.CountablyGenerated (Ring k) (Cokernel k) := sorry
-- Proof strategy: use the countable standard basis of `Free k` and descend its generating family
-- through the canonical quotient map onto `Cokernel k`.

/-- Example 15.15.5 (9): the cokernel of the square-zero shift is not projective. -/
@[stacks 05GR "Example 15.15.5 (9), nonprojective cokernel"]
theorem cokernel_not_projective : ¬ Module.Projective (Ring k) (Cokernel k) := sorry
-- Proof strategy: if the cokernel were projective, the canonical exact sequence from `map k` and
-- `injective k` would split, producing a linear retraction of `map k`; contradict `not_split k`.

/-- Example 15.15.5 (10): the cokernel of the square-zero shift is not Mittag-Leffler. -/
@[stacks 05GR "Example 15.15.5 (10), non-Mittag-Leffler cokernel"]
theorem cokernel_not_mittagLeffler : ¬ Module.MittagLeffler (Ring k) (Cokernel k) := sorry
-- Proof strategy: combine `cokernel_flat k` and `cokernel_countablyGenerated k` with the theorem
-- that a countably generated flat Mittag-Leffler module is projective, contradicting
-- `cokernel_not_projective k`.

end MvPolynomial.SquareZero.Shift
