module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Limit.FinitePresentation.IsoOverOpen

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

open AlgebraicGeometry

/- Remark 32.21.3 (1): the reduced closed subscheme on `T` maps to the limit of a cofinal
directed inverse system of open neighborhoods, compatibly over `S`, by a closed immersion. -/
@[stacks 0B3Y] #check
  (AlgebraicGeometry.Scheme.Limit.CofinalOpenNeighborhood.closedSubschemeLift_comp :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} {T : Set S} (hT : IsClosed T)
      (D : OrderDual I ⥤ Scheme.{u})
      (ι : D ⟶ (Functor.const (OrderDual I)).obj S)
      (c : Cone D) (hc : IsLimit c) (s : c.pt ⟶ S)
      (_ : ∀ i : OrderDual I, c.π.app i ≫ ι.app i = s)
      [∀ i : OrderDual I, IsOpenImmersion (ι.app i)]
      (hT_mem : ∀ i : OrderDual I, T ⊆
        (SetLike.coe (ι.app i).opensRange : Set S)),
      AlgebraicGeometry.Scheme.Limit.CofinalOpenNeighborhood.closedSubschemeLift
          hT D ι c hc hT_mem ≫ s =
        (AlgebraicGeometry.Scheme.ClosedSubschemeStructure.reduced ⟨T, hT⟩).ι)

#check
  (AlgebraicGeometry.Scheme.Limit.CofinalOpenNeighborhood.closedSubschemeLift_isClosedImmersion :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} {T : Set S} (hT : IsClosed T)
      (D : OrderDual I ⥤ Scheme.{u})
      (ι : D ⟶ (Functor.const (OrderDual I)).obj S)
      (c : Cone D) (hc : IsLimit c) (s : c.pt ⟶ S)
      (_ : ∀ i : OrderDual I, c.π.app i ≫ ι.app i = s)
      [∀ i : OrderDual I, IsOpenImmersion (ι.app i)]
      (hT_mem : ∀ i : OrderDual I, T ⊆
        (SetLike.coe (ι.app i).opensRange : Set S))
      (_ : ∀ W : S.Opens, T ⊆ (W : Set S) →
        ∃ i : OrderDual I, (ι.app i).opensRange ≤ W)
      [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))],
      IsClosedImmersion
        (AlgebraicGeometry.Scheme.Limit.CofinalOpenNeighborhood.closedSubschemeLift
          hT D ι c hc hT_mem))

/- Remark 32.21.3 (2): with quasi-compact complements and affine transition maps, base change to
the limit is an equivalence on finite-presentation morphisms that are isomorphisms over
`U = Tᶜ`. -/
@[stacks 0B3Y] #check
  (AlgebraicGeometry.FinitePresentationIsoOverOpen.baseChange_isEquivalence_of_cofinalOpenLimit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} {T : Set S} (_ : IsClosed T)
      (U : S.Opens) (_ : (U : Set S) = Tᶜ)
      (D : OrderDual I ⥤ Scheme.{u})
        (ι : D ⟶ (Functor.const (OrderDual I)).obj S)
        (c : Cone D) (_ : IsLimit c) (s : c.pt ⟶ S)
        (_ : ∀ i : OrderDual I, c.π.app i ≫ ι.app i = s)
        [∀ i : OrderDual I, IsOpenImmersion (ι.app i)]
        (_ : ∀ i : OrderDual I, T ⊆
          (SetLike.coe (ι.app i).opensRange : Set S))
        (_ : ∀ W : S.Opens, T ⊆ (W : Set S) →
          ∃ i : OrderDual I, (ι.app i).opensRange ≤ W)
        [∀ i : OrderDual I, QuasiCompact (((ι.app i) ⁻¹ᵁ U).ι)]
        [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))],
      Functor.IsEquivalence
        (AlgebraicGeometry.FinitePresentationIsoOverOpen.baseChange s U))
