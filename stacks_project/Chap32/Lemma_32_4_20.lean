/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.ClosedImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

/- Lemma 32.4.20: let `S` be a quasi-compact quasi-separated scheme, and let
`X = lim_i X_i` be a directed limit of quasi-compact quasi-separated schemes over `S` with affine
transition morphisms. If the transition morphisms `X_{i'} ⟶ X_i` are closed immersions, each
`X_i ⟶ S` is locally of finite type, and the limit morphism `X ⟶ S` is a closed immersion, then
`X_i ⟶ S` is a closed immersion for all sufficiently large `i`. -/
@[stacks 0A0N] #check
  (AlgebraicGeometry.Scheme.Limit.exists_eventually_isClosedImmersion_to_base_of_isLimit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] {S : Scheme.{u}}
      (D : OrderDual I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const (OrderDual I)).obj S)
      (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ S)
      (hπ : c.π ≫ t = (Functor.const _).map σlim)
      [CompactSpace S] [QuasiSeparatedSpace S]
      [∀ i : I, CompactSpace (D.obj i)]
      [∀ i : I, QuasiSeparatedSpace (D.obj i)]
      [∀ i : I, LocallyOfFiniteType (t.app i)]
      [∀ {i i' : I} (hii' : i ≤ i'), IsClosedImmersion (D.map (homOfLE hii'))]
      [IsClosedImmersion σlim],
      ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → IsClosedImmersion (t.app i))
