/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Int.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Sigma.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Words in a Graded Set

This leaf contains the concrete word combinatorics used by free graded
algebras.  It is independent of differentials and resolution constructions.
-/

universe v

namespace CochainDGAlgebra.Free

/-- The total degree of a word in a graded set is the sum of the degrees of its letters. -/
@[stacks 0BZ7 "graded word degree"]
def wordDegree (S : ℤ → Type v) : List (Sigma S) → ℤ
  | [] => 0
  | x :: xs => x.1 + wordDegree S xs

/-- The words in a graded set with a specified total degree. -/
@[stacks 0BZ7 "homogeneous words in graded generators"]
def WordsOfDegree (S : ℤ → Type v) (n : ℤ) : Type v :=
  { w : List (Sigma S) // wordDegree S w = n }

/-- The empty word has degree zero. -/
@[simp, stacks 0BZ7 "degree of the empty generator word"]
theorem wordDegree_nil (S : ℤ → Type v) :
    wordDegree S ([] : List (Sigma S)) = 0 := sorry

/-- Concatenating words adds their degrees. -/
@[simp, stacks 0BZ7 "degree of concatenated generator words"]
theorem wordDegree_append (S : ℤ → Type v) (u v : List (Sigma S)) :
    wordDegree S (u ++ v) = wordDegree S u + wordDegree S v := sorry

/-- Concatenating words of degrees `n` and `m` has degree `n + m`. -/
@[stacks 0BZ7 "degree of concatenated homogeneous generator words"]
theorem wordDegree_append_of_degree
    (S : ℤ → Type v) {n m : ℤ} (u : WordsOfDegree S n) (v : WordsOfDegree S m) :
    wordDegree S (u.1 ++ v.1) = n + m := sorry

/-- The empty word as a word of degree zero. -/
@[stacks 0BZ7 "unit word"]
def emptyWord (S : ℤ → Type v) : WordsOfDegree S 0 :=
  ⟨[], wordDegree_nil S⟩

/-- Concatenate homogeneous words. -/
@[stacks 0BZ7 "multiplication of homogeneous words"]
def appendWords
    (S : ℤ → Type v) {n m : ℤ} (u : WordsOfDegree S n) (v : WordsOfDegree S m) :
    WordsOfDegree S (n + m) :=
  ⟨u.1 ++ v.1, wordDegree_append_of_degree S u v⟩

end CochainDGAlgebra.Free
