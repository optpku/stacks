module

public import ReasLib.CategoryTheory.Filtration.Complex.BoundedReplacement
public import ReasLib.CategoryTheory.Filtration.Complex.Computation

/-!
# Bounded Filtered Replacements from Associated-Graded Vanishing

This file bridges the intrinsic replacement API for complexes in finite filtered objects to
termwise finite `FilteredComplex` objects.  It also records the source-facing formulations in
terms of vanishing associated-graded cohomology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex

open FilteredObject

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace Replace

namespace GE

/-- A termwise finite filtered complex with cohomologically bounded-below associated graded
admits a filtered quasi-isomorphism to a strictly bounded-below filtered complex. -/
@[stacks 05S5 "filtered bounded-below replacement"]
theorem exists_of_gr (K : FilteredComplex A) (hKfin : K.HasFiniteFiltrations) (a : ℤ)
    (hK : K.associatedGraded.IsGE a) :
    ∃ (L : FilteredComplex A) (_ : L.HasFiniteFiltrations) (f : K ⟶ L),
      QuasiIso (associatedGradedMap f) ∧ L.underlying.IsStrictlyGE a := sorry

/-- Lemma 13.13.8 (1): vanishing of associated-graded cohomology below `a` gives a termwise
finite filtered replacement that is strictly bounded below after forgetting the filtration. -/
@[stacks 05S5 "filtered bounded-below replacement"]
theorem exists_of_vanishes (K : FilteredComplex A) (hKfin : K.HasFiniteFiltrations) (a : ℤ)
    (hK : ∀ n : ℤ, n < a → IsZero (K.associatedGraded.homology n)) :
    ∃ (L : FilteredComplex A) (_ : L.HasFiniteFiltrations) (f : K ⟶ L),
      QuasiIso (associatedGradedMap f) ∧ L.underlying.IsStrictlyGE a := sorry

end GE

namespace LE

/-- A termwise finite filtered complex with cohomologically bounded-above associated graded
admits a filtered quasi-isomorphism from a strictly bounded-above filtered complex. -/
@[stacks 05S5 "filtered bounded-above replacement"]
theorem exists_of_gr (K : FilteredComplex A) (hKfin : K.HasFiniteFiltrations) (b : ℤ)
    (hK : K.associatedGraded.IsLE b) :
    ∃ (M : FilteredComplex A) (_ : M.HasFiniteFiltrations) (g : M ⟶ K),
      QuasiIso (associatedGradedMap g) ∧ M.underlying.IsStrictlyLE b := sorry

/-- Lemma 13.13.8 (2): vanishing of associated-graded cohomology above `b` gives a termwise
finite filtered replacement that is strictly bounded above after forgetting the filtration. -/
@[stacks 05S5 "filtered bounded-above replacement"]
theorem exists_of_vanishes (K : FilteredComplex A) (hKfin : K.HasFiniteFiltrations) (b : ℤ)
    (hK : ∀ n : ℤ, b < n → IsZero (K.associatedGraded.homology n)) :
    ∃ (M : FilteredComplex A) (_ : M.HasFiniteFiltrations) (g : M ⟶ K),
      QuasiIso (associatedGradedMap g) ∧ M.underlying.IsStrictlyLE b := sorry

end LE

namespace Square

/-- Complete lower and upper filtered replacements to a bounded comparison square.  The lower
cohomological bound is transported through the chosen filtered quasi-isomorphism `g`. -/
@[stacks 05S5 "filtered bounded comparison square"]
theorem exists_fill {K L M : FilteredComplex A} (hMfin : M.HasFiniteFiltrations) (a b : ℤ)
    (hK : K.associatedGraded.IsGE a) (f : K ⟶ L) (g : M ⟶ K)
    (hf : QuasiIso (associatedGradedMap f)) (hg : QuasiIso (associatedGradedMap g))
    (hL : L.underlying.IsStrictlyGE a) (hM : M.underlying.IsStrictlyLE b) :
    ∃ (N : FilteredComplex A) (_ : N.HasFiniteFiltrations) (u : M ⟶ N) (v : N ⟶ L),
      QuasiIso (associatedGradedMap u) ∧
        QuasiIso (associatedGradedMap v) ∧ CommSq u g v f ∧
        N.underlying.IsStrictlyGE a ∧ N.underlying.IsStrictlyLE b := sorry

end Square

namespace Bounded

/-- Explicit data of a bounded replacement square for `K` between the cohomological bounds
`a` and `b`.

The three replacement objects and four comparison maps are data.  Finiteness, associated-graded
quasi-isomorphism, commutativity, and strict support are recorded separately as proof fields, so
downstream constructions can select the diagram without unpacking a nested existential. -/
@[stacks 05S5 "explicit filtered bounded replacement square"]
structure Model (K : FilteredComplex A) (a b : ℤ) where
  /-- The replacement that is strictly bounded below by `a`. -/
  ge : FilteredComplex A
  /-- The replacement that is strictly bounded above by `b`. -/
  le : FilteredComplex A
  /-- The replacement that is strictly bounded on both sides. -/
  bounded : FilteredComplex A
  /-- The bounded-below replacement has termwise finite filtrations. -/
  geFinite : ge.HasFiniteFiltrations
  /-- The bounded-above replacement has termwise finite filtrations. -/
  leFinite : le.HasFiniteFiltrations
  /-- The two-sided bounded replacement has termwise finite filtrations. -/
  boundedFinite : bounded.HasFiniteFiltrations
  /-- The comparison from the original complex to the bounded-below replacement. -/
  toGE : K ⟶ ge
  /-- The comparison from the bounded-above replacement to the original complex. -/
  fromLE : le ⟶ K
  /-- The comparison from the bounded-above replacement to the two-sided bounded replacement. -/
  leToBounded : le ⟶ bounded
  /-- The comparison from the two-sided bounded replacement to the bounded-below replacement. -/
  boundedToGE : bounded ⟶ ge
  /-- The map to the bounded-below replacement is an associated-graded quasi-isomorphism. -/
  toGEQuasiIso : QuasiIso (associatedGradedMap toGE)
  /-- The map from the bounded-above replacement is an associated-graded quasi-isomorphism. -/
  fromLEQuasiIso : QuasiIso (associatedGradedMap fromLE)
  /-- The map into the two-sided bounded replacement is an associated-graded quasi-isomorphism. -/
  leToBoundedQuasiIso : QuasiIso (associatedGradedMap leToBounded)
  /-- The map out of the two-sided bounded replacement is an associated-graded quasi-isomorphism. -/
  boundedToGEQuasiIso : QuasiIso (associatedGradedMap boundedToGE)
  /-- The four comparison maps form a commutative square. -/
  commSq : CommSq leToBounded fromLE boundedToGE toGE
  /-- The bounded-below replacement is strictly supported in degrees at least `a`. -/
  geStrict : ge.underlying.IsStrictlyGE a
  /-- The bounded-above replacement is strictly supported in degrees at most `b`. -/
  leStrict : le.underlying.IsStrictlyLE b
  /-- The two-sided bounded replacement is strictly supported in degrees at least `a`. -/
  boundedGE : bounded.underlying.IsStrictlyGE a
  /-- The two-sided bounded replacement is strictly supported in degrees at most `b`. -/
  boundedLE : bounded.underlying.IsStrictlyLE b

namespace Model

/-- Cohomological support of the associated graded between fixed bounds yields an explicit
bounded replacement model. -/
@[stacks 05S5 "explicit filtered bounded replacement square"]
theorem nonempty_of_gr (K : FilteredComplex A) (hKfin : K.HasFiniteFiltrations) (a b : ℤ)
    (hGE : K.associatedGraded.IsGE a) (hLE : K.associatedGraded.IsLE b) :
    Nonempty (Model K a b) := sorry

/-- Associated-graded cohomology vanishing outside fixed bounds yields an explicit bounded
replacement model. -/
@[stacks 05S5 "explicit filtered bounded replacement square"]
theorem nonempty_of_vanishes (K : FilteredComplex A) (hKfin : K.HasFiniteFiltrations)
    (a b : ℤ) (hBelow : ∀ n : ℤ, n < a → IsZero (K.associatedGraded.homology n))
    (hAbove : ∀ n : ℤ, b < n → IsZero (K.associatedGraded.homology n)) :
    Nonempty (Model K a b) := sorry

/-- Eventual associated-graded cohomology vanishing selects bounds together with an explicit
bounded replacement model at those bounds. -/
@[stacks 05S5 "explicit filtered bounded replacement square"]
theorem exists_of_eventually_vanishes (K : FilteredComplex A)
    (hKfin : K.HasFiniteFiltrations)
    (hK : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.associatedGraded.homology n)) :
    ∃ a b : ℤ, Nonempty (Model K a b) := sorry

end Model

/-- A termwise finite filtered complex whose associated graded is cohomologically supported
between fixed bounds admits lower, upper, and bounded strict representatives in a commutative
square of filtered quasi-isomorphisms. -/
@[stacks 05S5 "filtered bounded replacement square"]
theorem exists_of_gr (K : FilteredComplex A) (hKfin : K.HasFiniteFiltrations) (a b : ℤ)
    (hGE : K.associatedGraded.IsGE a) (hLE : K.associatedGraded.IsLE b) :
    ∃ (L : FilteredComplex A) (_ : L.HasFiniteFiltrations) (f : K ⟶ L)
      (M : FilteredComplex A) (_ : M.HasFiniteFiltrations) (g : M ⟶ K)
      (N : FilteredComplex A) (_ : N.HasFiniteFiltrations) (u : M ⟶ N) (v : N ⟶ L),
      QuasiIso (associatedGradedMap f) ∧ QuasiIso (associatedGradedMap g) ∧
        QuasiIso (associatedGradedMap u) ∧ QuasiIso (associatedGradedMap v) ∧
        CommSq u g v f ∧ L.underlying.IsStrictlyGE a ∧ M.underlying.IsStrictlyLE b ∧
        N.underlying.IsStrictlyGE a ∧ N.underlying.IsStrictlyLE b := sorry

/-- Fixed lower and upper associated-graded cohomology vanishing bounds yield a bounded
comparison square of termwise finite filtered replacements. -/
@[stacks 05S5 "filtered bounded replacement square"]
theorem exists_of_vanishes (K : FilteredComplex A) (hKfin : K.HasFiniteFiltrations) (a b : ℤ)
    (hBelow : ∀ n : ℤ, n < a → IsZero (K.associatedGraded.homology n))
    (hAbove : ∀ n : ℤ, b < n → IsZero (K.associatedGraded.homology n)) :
    ∃ (L : FilteredComplex A) (_ : L.HasFiniteFiltrations) (f : K ⟶ L)
      (M : FilteredComplex A) (_ : M.HasFiniteFiltrations) (g : M ⟶ K)
      (N : FilteredComplex A) (_ : N.HasFiniteFiltrations) (u : M ⟶ N) (v : N ⟶ L),
      QuasiIso (associatedGradedMap f) ∧ QuasiIso (associatedGradedMap g) ∧
        QuasiIso (associatedGradedMap u) ∧ QuasiIso (associatedGradedMap v) ∧
        CommSq u g v f ∧ L.underlying.IsStrictlyGE a ∧ M.underlying.IsStrictlyLE b ∧
        N.underlying.IsStrictlyGE a ∧ N.underlying.IsStrictlyLE b := sorry

/-- Lemma 13.13.8 (3): eventual vanishing of associated-graded cohomology yields lower, upper,
and bounded termwise finite filtered representatives in a commutative square of filtered
quasi-isomorphisms. -/
@[stacks 05S5 "filtered bounded replacement square"]
theorem exists_of_eventually_vanishes (K : FilteredComplex A) (hKfin : K.HasFiniteFiltrations)
    (hK : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.associatedGraded.homology n)) :
    ∃ a b : ℤ,
      ∃ (L : FilteredComplex A) (_ : L.HasFiniteFiltrations) (f : K ⟶ L)
        (M : FilteredComplex A) (_ : M.HasFiniteFiltrations) (g : M ⟶ K)
        (N : FilteredComplex A) (_ : N.HasFiniteFiltrations) (u : M ⟶ N) (v : N ⟶ L),
        QuasiIso (associatedGradedMap f) ∧ QuasiIso (associatedGradedMap g) ∧
          QuasiIso (associatedGradedMap u) ∧ QuasiIso (associatedGradedMap v) ∧
          CommSq u g v f ∧ L.underlying.IsStrictlyGE a ∧ M.underlying.IsStrictlyLE b ∧
          N.underlying.IsStrictlyGE a ∧ N.underlying.IsStrictlyLE b := sorry

end Bounded

end Replace

end CategoryTheory.FilteredComplex
