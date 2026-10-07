module

public import ReasLib.Algebra.Homology.ChainComplex.Exact
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded complexes with chosen finite free coordinates

This data owner records a bounded chain complex together with explicit finite
free coordinate models for its terms.  The coordinate data are essential for
matrix-minor invariants, so they are retained rather than hidden behind a
basis-free wrapper.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits ChainComplex

section

variable {R : Type u} [Ring R]

/-- Situation 10.102.1: a bounded chain complex of finite free `R`-modules equipped with
chosen standard-coordinate presentations. -/
@[stacks 00MS "finite free complexes"]
structure FiniteFreeComplex (R : Type u) [Ring R] (e : ℕ) where
  /-- The underlying chain complex of `R`-modules. -/
  toChainComplex : ChainComplex (ModuleCat R) ℕ
  /-- The complex is zero in degrees strictly above `e`. -/
  isZero_toChainComplex_X : ∀ i : ℕ, e < i → Limits.IsZero (toChainComplex.X i)
  /-- The ranks of the chosen standard finite free coordinate models. -/
  rank : Fin (e + 1) → ℕ
  /-- The coordinate identification of each displayed term with `Fin (rank i) → R`. -/
  termIso :
    ∀ i : Fin (e + 1),
      toChainComplex.X i ≅ ModuleCat.of R (Fin (rank i) → R)

namespace FiniteFreeComplex

variable {e : ℕ} (C : _root_.FiniteFreeComplex R e)

/-- The index of the `k`th term in the alternating tail beginning after degree `i`. -/
def alternatingRankIndex (i : Fin e) (k : Fin (e - i)) : Fin (e + 1) :=
  ⟨i.1 + 1 + k.1, by omega⟩

/-- Positions at which a bounded complex has two adjacent displayed differentials. -/
@[stacks 00MS "adjacent finite-free differential indices"]
abbrev AdjacentIndex (e : ℕ) := Fin (e - 1)

namespace AdjacentIndex

/-- The lower differential at an adjacent position. -/
@[stacks 00MS "lower adjacent differential index"]
def lower (i : AdjacentIndex e) : Fin e := ⟨i, by omega⟩

/-- The upper differential at an adjacent position. -/
@[stacks 00MS "upper adjacent differential index"]
def upper (i : AdjacentIndex e) : Fin e := ⟨i + 1, by omega⟩

/-- The common term of the two adjacent differentials. -/
@[stacks 00MS "common term of adjacent differentials"]
def term (i : AdjacentIndex e) : Fin (e + 1) := ⟨i + 1, by omega⟩

@[simp] theorem lower_val (i : AdjacentIndex e) : i.lower.val = i.val := rfl
@[simp] theorem upper_val (i : AdjacentIndex e) : i.upper.val = i.val + 1 := rfl
@[simp] theorem term_val (i : AdjacentIndex e) : i.term.val = i.val + 1 := rfl

end AdjacentIndex

/-- The standard finite free module chosen for the term indexed by `i`. -/
abbrev term (i : Fin (e + 1)) : Type u :=
  Fin (C.rank i) → R

/-- The chosen coordinate identification for the term indexed by `i`. -/
abbrev termIsoAt (i : Fin (e + 1)) :
    C.toChainComplex.X i ≅ ModuleCat.of R (C.term i) :=
  C.termIso i

/-- The differential in standard coordinates between two consecutive displayed degrees. -/
abbrev differential (i : ℕ) (hi : i < e) :
    C.term ⟨i + 1, Nat.succ_lt_succ hi⟩ →ₗ[R] C.term ⟨i, Nat.lt_succ_of_lt hi⟩ :=
  ((C.termIsoAt ⟨i + 1, Nat.succ_lt_succ hi⟩).inv ≫
      C.toChainComplex.d (i + 1) i ≫
      (C.termIsoAt ⟨i, Nat.lt_succ_of_lt hi⟩).hom).hom

/-- The displayed differential from degree `i + 1` to degree `i`. -/
abbrev diffAt (i : Fin e) : C.term i.succ →ₗ[R] C.term i.castSucc :=
  C.differential i i.isLt

namespace diffAt

/-- The source coordinate isomorphism intertwines a displayed differential with the underlying
chain-complex differential. -/
@[reassoc, stacks 00MS "finite-free differential coordinate square"]
theorem termIso_hom_comp (i : Fin e) :
    (C.termIso i.succ).hom ≫ ModuleCat.ofHom (C.diffAt i) =
      C.toChainComplex.d (i.1 + 1) i.1 ≫ (C.termIso i.castSucc).hom := sorry

/-- Postcomposing a displayed differential with the target coordinate inverse recovers the
underlying differential in source coordinates. -/
@[reassoc, stacks 00MS "finite-free differential inverse coordinate square"]
theorem comp_termIso_inv (i : Fin e) :
    ModuleCat.ofHom (C.diffAt i) ≫ (C.termIso i.castSucc).inv =
      (C.termIso i.succ).inv ≫ C.toChainComplex.d (i.1 + 1) i.1 := sorry

/-- Conjugating a displayed differential through both chosen term coordinates recovers the
underlying chain-complex differential. -/
@[reassoc, stacks 00MS "finite-free differential coordinate conjugation"]
theorem conjugate (i : Fin e) :
    (C.termIso i.succ).hom ≫ ModuleCat.ofHom (C.diffAt i) ≫
        (C.termIso i.castSucc).inv =
      C.toChainComplex.d (i.1 + 1) i.1 := sorry

/-- Pointwise form of `diffAt.comp_termIso_inv`. -/
@[stacks 00MS "finite-free differential coordinate evaluation"]
theorem termIso_inv_apply (i : Fin e) (v : C.term i.succ) :
    (C.termIso i.castSucc).inv.hom (C.diffAt i v) =
      (C.toChainComplex.d (i.1 + 1) i.1).hom ((C.termIso i.succ).inv.hom v) := sorry

/-- Injectivity of a displayed differential is equivalent to injectivity of the corresponding
underlying chain-complex differential. -/
@[stacks 00MS "finite-free differential injectivity"]
theorem injective_iff (i : Fin e) :
    Function.Injective (C.diffAt i) ↔
      Function.Injective ((C.toChainComplex.d (i.1 + 1) i.1).hom) := sorry

end diffAt

/-- A displayed term with rank zero is a zero object. -/
@[stacks 00MS "rank-zero finite-free term"]
theorem isZero_X_of_rank_eq_zero (j : Fin (e + 1)) (hj : C.rank j = 0) :
    IsZero (C.toChainComplex.X j) := sorry

/-- The alternating sum of the ranks in the tail starting at degree `i + 1`. -/
def alternatingRank (i : Fin e) : ℤ :=
  List.alternatingSum <|
    List.ofFn fun k : Fin (e - i) ↦ (C.rank (alternatingRankIndex i k) : ℤ)

namespace alternatingRank

/-- Alternating tails at adjacent indices add to the rank of their common term. -/
@[stacks 00MS "adjacent alternating-rank tails"]
theorem lower_add_upper (i : AdjacentIndex e) :
    C.alternatingRank i.lower + C.alternatingRank i.upper =
      (C.rank i.term : ℤ) := sorry

end alternatingRank

/-! ### Positive rank profiles -/

section RankProfile

variable {e : ℕ}

/-- The total rank in the positive degrees of a bounded rank profile. -/
@[stacks 00MS "positive-degree rank profile sum"]
def positiveRankSumProfile (n : Fin (e + 1) → ℕ) : ℕ :=
  ∑ j : Fin e, n j.succ

namespace positiveRankSumProfile

/-- Every positive-degree rank is bounded by the profile sum. -/
@[stacks 00MS "positive rank profile summand bound"]
theorem rank_succ_le (n : Fin (e + 1) → ℕ) (j : Fin e) :
    n j.succ ≤ positiveRankSumProfile n := sorry

/-- A zero positive-degree profile sum forces every positive-degree rank to vanish. -/
@[stacks 00MS "zero positive rank profile"]
theorem rank_succ_eq_zero_of_eq_zero
    (n : Fin (e + 1) → ℕ) (hzero : positiveRankSumProfile n = 0) (j : Fin e) :
    n j.succ = 0 := sorry

end positiveRankSumProfile

/-- The positive-degree rank sum of a bounded finite free complex. -/
@[stacks 00MS "positive-degree rank sum of a finite-free complex"]
def positiveRankSum (C : _root_.FiniteFreeComplex R e) : ℕ :=
  positiveRankSumProfile C.rank

namespace positiveRankSum

/-- Every positive-degree displayed rank is bounded by the complex rank sum. -/
@[stacks 00MS "finite-free positive rank summand bound"]
theorem rank_succ_le (C : _root_.FiniteFreeComplex R e) (j : Fin e) :
    C.rank j.succ ≤ positiveRankSum C :=
  sorry

/-- A zero positive-degree rank sum forces every positive displayed rank to vanish. -/
@[stacks 00MS "zero finite-free positive rank sum"]
theorem rank_succ_eq_zero_of_eq_zero
    (C : _root_.FiniteFreeComplex R e) (hzero : positiveRankSum C = 0) (j : Fin e) :
    C.rank j.succ = 0 := sorry

end positiveRankSum

end RankProfile

/-- Each displayed coordinate term is a free `R`-module. -/
@[stacks 00MS "finite-free coordinate term freeness"]
instance (i : Fin (e + 1)) : Module.Free R (C.term i) := inferInstance

/-- Each displayed coordinate term is a finite `R`-module. -/
@[stacks 00MS "finite-free coordinate term finiteness"]
instance (i : Fin (e + 1)) : Module.Finite R (C.term i) := inferInstance

/-- The underlying chain complex is termwise free. -/
@[stacks 00MS "finite-free complex termwise freeness"]
theorem isTermwiseFree : ChainComplex.IsTermwiseFree C.toChainComplex := sorry

/-- The underlying chain complex is termwise finite. -/
@[stacks 00MS "finite-free complex termwise finiteness"]
theorem isTermwiseFinite : ChainComplex.IsTermwiseFinite C.toChainComplex := sorry

/-- Each term of the underlying chain complex is a free module. -/
@[stacks 00MS "finite-free underlying term freeness"]
instance (i : ℕ) : Module.Free R (C.toChainComplex.X i) :=
  C.isTermwiseFree i

/-- Each term of the underlying chain complex is a finite module. -/
@[stacks 00MS "finite-free underlying term finiteness"]
instance (i : ℕ) : Module.Finite R (C.toChainComplex.X i) :=
  C.isTermwiseFinite i

/-- The source-facing positive-degree exactness predicate, restricted to the nonzero range of
a bounded finite free complex. -/
@[stacks 00MS "positive-degree exactness for finite-free complexes"]
def ExactInPositiveDegrees (C : _root_.FiniteFreeComplex R e) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ e → C.toChainComplex.ExactAt j

/-- For a bounded finite free complex, checking the displayed range is equivalent to exactness in
all positive chain degrees. -/
@[stacks 00MS "positive-degree exactness characterization"]
theorem exactInPositiveDegrees_iff_chainComplex :
    C.ExactInPositiveDegrees ↔ ChainComplex.ExactInPositiveDegrees C.toChainComplex := sorry

/-- The short complex formed by two consecutive differentials in degrees `i + 2 → i + 1 → i`. -/
@[stacks 00MS "finite-free adjacent short complex"]
abbrev shortComplexAt (i : ℕ) : ShortComplex (ModuleCat R) :=
  ShortComplex.mk
    (C.toChainComplex.d (i + 2) (i + 1))
    (C.toChainComplex.d (i + 1) i)
    (C.toChainComplex.d_comp_d (i + 2) (i + 1) i)

end FiniteFreeComplex

end
