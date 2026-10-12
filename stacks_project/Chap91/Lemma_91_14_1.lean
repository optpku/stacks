/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap76.Lemma_76_9_2_Thickening
public import stacks_project.Chap91.Situation_91_9_1_Thickening
import Mathlib.Tactic.CrossRefAttribute

/-!
# Thickenings of algebraic spaces versus thickenings of small étale ringed topoi

A morphism of algebraic spaces is a thickening if and only if the associated morphism of
small étale ringed topoi is a thickening of ringed topoi.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 91.14.1: for a morphism `i : Z ⟶ Z'` of algebraic spaces over a scheme `S`,
`i` is a thickening of algebraic spaces if and only if the associated morphism
`i_small := ringedToposHom i` of small étale ringed topoi
`(Sh(Z_étale), 𝒪_Z) = ringedSite Z` to `(Sh(Z'_étale), 𝒪_Z') = ringedSite Z'`
is a thickening of ringed topoi. -/
@[stacks 0D16]
theorem isThickening_iff_ringedToposHom {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') :
    IsThickening i ↔ RingedSite.ToposHom.IsThickening (ringedToposHom i) :=
  sorry

/-- A thickening of algebraic spaces induces a thickening of the associated small étale
ringed topoi. -/
instance instIsThickening_ringedToposHom {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsThickening i] :
    RingedSite.ToposHom.IsThickening.{u + 1, u, u + 1, u, u} (ringedToposHom i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
