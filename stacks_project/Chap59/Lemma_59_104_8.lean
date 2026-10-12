/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_104_8_OverH
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.EtaleSheaf

universe u v

namespace AlgebraicGeometry.Scheme.EtaleSheaf

/-- Lemma 59.104.8: for a scheme `S` in a chosen big h site, the category over
`(Sch/S)_h` whose fibre over `U` is `Sh(U_étale)` (Type-valued sheaves on the
small étale site of `U`) is a stack, via the CoGrothendieck projection
`overForget` of `overPseudofunctor`. -/
@[stacks 0GF5, instance]
instance overPseudofunctor_isStack (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier) :
    Pseudofunctor.IsStack (overPseudofunctor Schh S)
      (ChosenBigHSite.bigTopology Schh S) :=
  sorry

end AlgebraicGeometry.Scheme.EtaleSheaf
