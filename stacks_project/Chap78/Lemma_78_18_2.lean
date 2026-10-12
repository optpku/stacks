/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap78.Lemma_78_18_2_InvariantOpen

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Lemma 78.18.2 (1): let `B → S` as in Section 78.3, and let `(U, R, s, t, c)` be a
groupoid in algebraic spaces over `B`. If `s` and `t` are open, then for every
open `W ⊂ U` the open `s(t⁻¹(W))` is `R`-invariant. -/
@[stacks 044G]
theorem isOpenInvariant_sImageTPreimage {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Open G.s.left] [AlgebraicSpace.Open G.t.left]
    (W : OpenSubspace G.U.left) :
    G.toPreRelation.IsOpenInvariant (sImageTPreimage G W) := sorry

/-- Lemma 78.18.2 (2): let `B → S` as in Section 78.3, and let `(U, R, s, t, c)` be a
groupoid in algebraic spaces over `B`. If `s` and `t` are open and quasi-compact,
then `U` has an open covering consisting of `R`-invariant quasi-compact open
subspaces. -/
@[stacks 044G]
theorem exists_invariantQuasiCompactOpenCover {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Open G.s.left] [AlgebraicSpace.Open G.t.left]
    [AlgebraicSpace.QuasiCompact G.s.left] [AlgebraicSpace.QuasiCompact G.t.left] :
    ∃ (ι : Type u) (_ : Small.{u} ι) (𝒰 : ι → OpenSubspace G.U.left),
      IsZariskiCover G.U.left (fun i ↦ (𝒰 i).X) (fun i ↦ (𝒰 i).ι) ∧
        ∀ i, G.toPreRelation.IsOpenInvariant (𝒰 i) ∧ IsQuasiCompact (𝒰 i).X := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
