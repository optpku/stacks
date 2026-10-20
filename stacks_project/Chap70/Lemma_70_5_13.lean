module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.Separated
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 70.5.13: let `Y` be a quasi-separated algebraic space over `S`, and let
`X = lim_i X_i` be a directed limit of quasi-compact quasi-separated algebraic
spaces over `Y` with affine transition morphisms. If the limit structure morphism
`X ⟶ Y` is separated, then the stage structure morphisms `X_i ⟶ Y` are separated
for all sufficiently large `i`. -/
@[stacks 086X] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.exists_eventually_isSeparated_to_base_of_isLimit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} {Y : AlgebraicSpace S}
      (D : OrderDual I ⥤ AlgebraicSpace S)
      (t : D ⟶ (Functor.const (OrderDual I)).obj Y)
      (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ Y)
      (hπ : c.π ≫ t = (Functor.const _).map σlim)
      [IsAbsolutelyQuasiSeparated Y]
      [∀ i : I, IsQuasiCompact (D.obj i)]
      [∀ i : I, IsAbsolutelyQuasiSeparated (D.obj i)]
      [∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))]
      [Separated σlim],
      ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → Separated (t.app i))
