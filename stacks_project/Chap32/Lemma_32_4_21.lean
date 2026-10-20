module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Immersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

/- Lemma 32.4.21: let `S` be a quasi-separated scheme, and let `X = lim_i X_i` be a directed
limit of quasi-compact quasi-separated schemes over `S`. If the transition morphisms
`X_{i'} ⟶ X_i` are closed immersions, each `X_i ⟶ S` is locally of finite type, and the limit
morphism `X ⟶ S` is an immersion, then `X_i ⟶ S` is an immersion for all sufficiently large
`i`. -/
@[stacks 0GIH] #check
  (AlgebraicGeometry.Scheme.Limit.exists_eventually_isImmersion_to_base_of_isLimit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] {S : Scheme.{u}}
      (D : OrderDual I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const (OrderDual I)).obj S)
      (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ S)
      (hπ : c.π ≫ t = (Functor.const _).map σlim)
      [QuasiSeparatedSpace S]
      [∀ i : I, CompactSpace (D.obj i)]
      [∀ i : I, QuasiSeparatedSpace (D.obj i)]
      [∀ i : I, LocallyOfFiniteType (t.app i)]
      [∀ {i i' : I} (hii' : i ≤ i'), IsClosedImmersion (D.map (homOfLE hii'))]
      [IsImmersion σlim],
      ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → IsImmersion (t.app i))
