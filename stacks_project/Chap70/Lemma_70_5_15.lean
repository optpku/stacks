module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.Finite
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 70.5.15: let `Y` be a quasi-compact quasi-separated algebraic space over
`S`, and let `X = lim_i X_i` be a directed limit of quasi-compact quasi-separated
algebraic spaces over `Y` with finite transition morphisms. If every stage
morphism `X_i ⟶ Y` is locally of finite type and the limit structure morphism
`X ⟶ Y` is integral, then the stage structure morphisms `X_i ⟶ Y` are finite
for all sufficiently large `i`. -/
@[stacks 0A0S] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.exists_eventually_isFinite_to_base_of_isLimit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} {Y : AlgebraicSpace S}
      (D : OrderDual I ⥤ AlgebraicSpace S)
      (t : D ⟶ (Functor.const (OrderDual I)).obj Y)
      (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ Y)
      (hπ : c.π ≫ t = (Functor.const _).map σlim)
      [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
      [∀ i : I, IsQuasiCompact (D.obj i)]
      [∀ i : I, IsAbsolutelyQuasiSeparated (D.obj i)]
      [∀ {i i' : I} (hii' : i ≤ i'), AlgebraicSpace.IsFinite (D.map (homOfLE hii'))]
      [∀ i : I, AlgebraicSpace.LocallyOfFiniteType (t.app i)]
      [AlgebraicSpace.IsIntegralHom σlim],
      ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → AlgebraicSpace.IsFinite (t.app i))
