/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Lemma_70_5_14_Affine
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 70.5.14: let `Y` be a quasi-compact quasi-separated algebraic space over
`S`, and let `X = lim_i X_i` be a directed limit of quasi-compact quasi-separated
algebraic spaces over `Y` with affine transition morphisms. If the limit structure
morphism `X ⟶ Y` is affine, then the stage structure morphisms `X_i ⟶ Y` are
affine for all sufficiently large `i`. -/
@[stacks 0A0R] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.exists_eventually_isAffine_to_base_of_isLimit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} {Y : AlgebraicSpace S}
      (D : OrderDual I ⥤ AlgebraicSpace S)
      (t : D ⟶ (Functor.const (OrderDual I)).obj Y)
      (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ Y)
      (hπ : c.π ≫ t = (Functor.const _).map σlim)
      [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
      [∀ i : I, IsQuasiCompact (D.obj i)]
      [∀ i : I, IsAbsolutelyQuasiSeparated (D.obj i)]
      [∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))]
      [Affine σlim],
      ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → Affine (t.app i))
