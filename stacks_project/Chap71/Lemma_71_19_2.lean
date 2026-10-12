/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Lemma_71_19_3_AdmissibleBlowup
public import stacks_project.Chap71.Lemma_71_19_4_CommonRefinement

/-!
# Composition of successive admissible blowups

Successive blowups of a quasi-compact quasi-separated algebraic space that are
admissible over a quasi-compact open subspace compose to a blowup admissible
over the same open subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 71.19.2: let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space over `S`. Let `U ⊂ X` be a quasi-compact open
subspace. Let `b : X' ⟶ X` be a `U`-admissible blowup, and let `b' : X'' ⟶ X'`
be a `U`-admissible blowup, with `U` viewed on `X'` as `U.inverseImage b`. Then
the composition `b' ≫ b` is a `U`-admissible blowup. -/
@[stacks 086C]
theorem IsAdmissibleBlowup.comp {S : Scheme.{u}} {X X' X'' : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (U : OpenSubspace X) [QuasiCompact U.ι]
    (b : X' ⟶ X) (hb : IsAdmissibleBlowup U b)
    (b' : X'' ⟶ X') (hb' : IsAdmissibleBlowup (U.inverseImage b) b') :
    IsAdmissibleBlowup U (b' ≫ b) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
