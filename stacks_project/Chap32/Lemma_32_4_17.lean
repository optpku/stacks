/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Separated
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

/- Lemma 32.4.17: let `S` be a scheme and let `X = lim_i X_i` be a directed limit of schemes
over `S` with affine transition morphisms. Assume `S` is quasi-separated, every `X_i` is
quasi-compact and quasi-separated, and the limit structure morphism `X ⟶ S` is separated. Then
the stage structure morphisms `X_i ⟶ S` are separated for all sufficiently large `i`. -/
@[stacks 01ZH] #check
  (AlgebraicGeometry.Scheme.Limit.exists_eventually_isSeparated_to_base_of_isLimit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] {S : Scheme.{u}}
      (D : OrderDual I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const (OrderDual I)).obj S)
      (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ S)
      (hπ : c.π ≫ t = (Functor.const _).map σlim)
      [QuasiSeparatedSpace S]
      [∀ i : I, CompactSpace (D.obj i)]
      [∀ i : I, QuasiSeparatedSpace (D.obj i)]
      [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))]
      [IsSeparated σlim],
      ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → IsSeparated (t.app i))
