module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Splitting.Monic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restricting chosen splittings between truncation levels

This module restricts a chosen `n`-truncated splitting along a comparison `m ≤ n` and records
its identity, composition, monicity, and splitness API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped SimplexCategory.Truncated

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {C : Type u} [Category.{v} C]

namespace Splitting

namespace trunc

/-- The restricted splitting cofan is colimiting after passing between truncation levels. -/
@[stacks 017P "colimit decomposition after further truncating a splitting"]
def isColimit {n m : ℕ} {X : SimplicialObject.Truncated C n}
    (s : Splitting X) (h : m ≤ n)
    (Δ : (SimplexCategory.Truncated m)ᵒᵖ) :
    IsColimit (cofan'
      (fun i : Fin (m + 1) ↦ s.N (Fin.castLE (Nat.succ_le_succ h) i))
      ((Truncated.trunc C n m h).obj X)
      (fun i : Fin (m + 1) ↦ s.ι (Fin.castLE (Nat.succ_le_succ h) i)) Δ) :=
  s.isColimit (op ((SimplexCategory.Truncated.incl m n h).obj Δ.unop))

end trunc

/-- Restrict a chosen `n`-truncated splitting to any lower truncation level `m ≤ n`. -/
@[stacks 017P "further truncation of a chosen splitting"]
def trunc {n m : ℕ} {X : SimplicialObject.Truncated C n}
    (s : Splitting X) (h : m ≤ n) :
    Splitting ((Truncated.trunc C n m h).obj X) where
  N i := s.N (Fin.castLE (Nat.succ_le_succ h) i)
  ι i := s.ι (Fin.castLE (Nat.succ_le_succ h) i)
  isColimit' := trunc.isColimit s h

/-- Further truncation retains the chosen summand in every remaining degree. -/
@[simp, stacks 017P "summands after further truncating a splitting"]
theorem trunc_N {n m : ℕ} {X : SimplicialObject.Truncated C n}
    (s : Splitting X) (h : m ≤ n) (i : Fin (m + 1)) :
    (s.trunc h).N i = s.N (Fin.castLE (Nat.succ_le_succ h) i) := sorry

/-- Further truncation retains the distinguished map in every remaining degree. -/
@[simp, stacks 017P "summand maps after further truncating a splitting"]
theorem trunc_ι {n m : ℕ} {X : SimplicialObject.Truncated C n}
    (s : Splitting X) (h : m ≤ n) (i : Fin (m + 1)) :
    (s.trunc h).ι i = s.ι (Fin.castLE (Nat.succ_le_succ h) i) := sorry

namespace IsMonic

/-- Further truncation preserves an explicit proof that a chosen truncated splitting is
monic. -/
@[stacks 017P "monicity after further truncating a splitting"]
theorem trunc {n m : ℕ} {X : SimplicialObject.Truncated C n} {s : Splitting X}
    (hs : s.IsMonic) (h : m ≤ n) : (s.trunc h).IsMonic := sorry

end IsMonic

namespace trunc

/-- Typeclass transport of monicity along restriction between truncation levels. -/
@[stacks 017P "monicity instance after further truncating a splitting"]
instance isMonic {n m : ℕ} {X : SimplicialObject.Truncated C n}
    (s : Splitting X) [s.IsMonic] (h : m ≤ n) :
    (s.trunc h).IsMonic := sorry

/-- Restricting chosen splitting data along the identity comparison changes no data. -/
@[simp, stacks 017P "identity law for further truncating a splitting"]
theorem id {n : ℕ} {X : SimplicialObject.Truncated C n} (s : Splitting X) :
    s.trunc (le_refl n) = s := sorry

/-- Successive restrictions of chosen splitting data agree with restriction along the composite
comparison. -/
@[simp, stacks 017P "composition law for further truncating a splitting"]
theorem comp {n m l : ℕ} {X : SimplicialObject.Truncated C n}
    (s : Splitting X) (h : m ≤ n) (g : l ≤ m) :
    (s.trunc h).trunc g = s.trunc (g.trans h) := sorry

end trunc

end Splitting

namespace IsSplit

/-- Splitness descends along every further truncation. -/
@[stacks 017P "splitness after further truncation"]
theorem trunc {n m : ℕ} {X : SimplicialObject.Truncated C n}
    (hX : IsSplit X) (h : m ≤ n) :
    IsSplit ((Truncated.trunc C n m h).obj X) := sorry

end IsSplit

end CategoryTheory.SimplicialObject.Truncated
