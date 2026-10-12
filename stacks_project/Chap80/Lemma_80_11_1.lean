/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf
public import stacks_project.Chap65.Lemma_65_16_4_IsAlgebraicSpace

/-!
# Fppf locality of algebraic spaces

A sheaf which is fppf locally an algebraic space is an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 80.11.1: let `S` be a scheme. Let `F : (Over S)ᵒᵖ ⥤ Type u` be a
functor. Let `{S_i → S}_{i ∈ I}` be a covering of `(Sch/S)_fppf`. If `F` is an
fppf sheaf, each `F_i = yoneda.obj (S_i) ⨯ F` is an algebraic space, and
`[Small.{u} I]` is the size condition of Spaces, Lemma 65.8.4 making
`∐ F_i` an algebraic space, then `F` is an algebraic space. Assumption (2) is
equivalent to the restriction of `F` along `S_i` being an algebraic space
(Spaces, Lemma 65.16.4). -/
@[stacks 04SK]
theorem IsAlgebraicSpace.of_fppfLocal {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {I : Type v} [Small.{u} I] (Si : I → Over S) (hSi : Scheme.FppfCovering Si)
    (hFi : ∀ i, IsAlgebraicSpace (yoneda.obj (Si i) ⨯ F)) :
    IsAlgebraicSpace F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
