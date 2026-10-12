/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Affine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

/- Lemma 32.4.18: for a directed inverse system of quasi-compact and quasi-separated schemes
over a quasi-compact and quasi-separated base, with affine transition morphisms and affine
limit-to-base morphism, the stage-to-base morphisms are affine at every sufficiently late stage. -/
@[stacks 09ZM] #check
  (AlgebraicGeometry.Scheme.Limit.exists_eventually_isAffineHom_to_base_of_isLimit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] {S : Scheme.{u}}
      (D : OrderDual I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const (OrderDual I)).obj S)
      (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ S)
      (hπ : c.π ≫ t = (Functor.const _).map σlim)
      [CompactSpace S] [QuasiSeparatedSpace S]
      [∀ i : I, CompactSpace (D.obj i)]
      [∀ i : I, QuasiSeparatedSpace (D.obj i)]
      [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))]
      [IsAffineHom σlim],
      ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → IsAffineHom (t.app i))
