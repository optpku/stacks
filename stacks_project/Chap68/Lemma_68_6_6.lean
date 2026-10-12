/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.Lemma_68_17_4_Relative

/-!
# Étale ascent of decent and reasonable algebraic spaces

If `f : X ⟶ Y` is an étale morphism of algebraic spaces over a scheme `S`, then
decency and reasonableness of `Y` pass to `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsDecent

/-- Lemma 68.6.6 (1): Let `S` be a scheme. If `f : X ⟶ Y` is an étale morphism of
algebraic spaces over `S` and `Y` is decent, then `X` is decent. -/
@[stacks 0ABU]
theorem of_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Etale f] [IsDecent Y] : IsDecent X := sorry

end IsDecent

namespace IsReasonable

/-- Lemma 68.6.6 (2): Let `S` be a scheme. If `f : X ⟶ Y` is an étale morphism of
algebraic spaces over `S` and `Y` is reasonable, then `X` is reasonable. -/
@[stacks 0ABU]
theorem of_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Etale f] [IsReasonable Y] : IsReasonable X := sorry

end IsReasonable

end AlgebraicGeometry.AlgebraicSpace
