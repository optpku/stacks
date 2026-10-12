/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Definition_98_23_5_AffineOpen
public import stacks_project.Chap98.Definition_98_23_5_Obstruction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.GroupoidsOver

/- Definition 98.23.5: let S be a locally Noetherian base and let X be a
category fibred in groupoids over (Sch/S)_fppf satisfying (RS*). A naive
obstruction theory assigns, to every S-algebra A such that Spec(A) ⟶ S factors
through an affine open Spec(Λ) ⊂ S and every object x of X over Spec(A), a
complex E_x in D⁻(A) and a map ξ_x : E_x ⟶ NL{A⁄Λ}; isomorphisms of functors
Inf_x ≅ Ext^{-1}_A(E_x, -) and T_x ≅ Ext^0_A(E_x, -); and functoriality maps
E_x ⟶ E_y in D(A) along A → B with y = x|_Spec(B). These data make diagram (i)
commute, compose, match the maps of Remark 98.21.3, send ξ_x composed with
NL ⟶ Ω to the canonical element of T_x(Ω[A⁄Λ]), and detect lifts of a
deformation situation (x, A' → A) by vanishing of
E_x ⟶ NL{A⁄Λ} ⟶ NL{A⁄A'}. -/
@[stacks 07YP]
#check NaiveObstructionTheory

#check NaiveObstructionTheory.spec_infIso_natural

#check NaiveObstructionTheory.spec_tangentIso_natural

#check NaiveObstructionTheory.spec_canonical_compat

#check NaiveObstructionTheory.lifts_iff_zero
