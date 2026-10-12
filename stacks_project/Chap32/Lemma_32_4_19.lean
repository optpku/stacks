/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Finite
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

/- Lemma 32.4.19: let `S` be a scheme and let `X = lim_i X_i` be a directed limit of schemes
over `S` with finite transition morphisms. Assume `S` and every `X_i` are quasi-compact and
quasi-separated, every `X_i ⟶ S` is locally of finite type, and the limit morphism `X ⟶ S` is
integral. Then `X_i ⟶ S` is finite for all sufficiently large `i`. -/
@[stacks 09ZN] #check
  (AlgebraicGeometry.Scheme.Limit.exists_eventually_isFinite_to_base_of_isLimit_isIntegralHom :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] {S : Scheme.{u}}
      (D : OrderDual I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const (OrderDual I)).obj S)
      (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ S)
      (hπ : c.π ≫ t = (Functor.const _).map σlim)
      [CompactSpace S] [QuasiSeparatedSpace S]
      [∀ i : I, CompactSpace (D.obj i)]
      [∀ i : I, QuasiSeparatedSpace (D.obj i)]
      [∀ {i i' : I} (hii' : i ≤ i'), IsFinite (D.map (homOfLE hii'))]
      [∀ i : I, LocallyOfFiniteType (t.app i)]
      [IsIntegralHom σlim],
      ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → IsFinite (t.app i))
