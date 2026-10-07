module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.CofinalOpenNeighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.IsoOverOpen.BaseChange

/-!
# Finite-presentation morphisms over limits of open neighborhoods

This module records the invariance of finite-presentation morphisms that are
isomorphisms away from a closed subset under passage to a limit of a cofinal
directed system of open neighborhoods.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FinitePresentationIsoOverOpen

/-- Let `T` be a closed subset of a scheme `S`, and let `U = Tᶜ`. Suppose a directed
inverse system consists of open neighborhoods of `T`, cofinal among all such neighborhoods,
with quasi-compact complements and affine transition maps. Base change from `S` to a scheme
limit of this system is an equivalence on finite-presentation morphisms that are isomorphisms
over `U`. -/
theorem baseChange_isEquivalence_of_cofinalOpenLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {T : Set S} (hT : IsClosed T)
    (U : S.Opens) (hU : (U : Set S) = Tᶜ)
    (D : OrderDual I ⥤ Scheme.{u})
    (ι : D ⟶ (Functor.const (OrderDual I)).obj S)
    (c : Cone D) (hc : IsLimit c) (s : c.pt ⟶ S)
    (hπ : ∀ i : OrderDual I, c.π.app i ≫ ι.app i = s)
    [∀ i : OrderDual I, IsOpenImmersion (ι.app i)]
    (hT_mem : ∀ i : OrderDual I, T ⊆
      (SetLike.coe (ι.app i).opensRange : Set S))
    (hι_cofinal : ∀ W : S.Opens, T ⊆ (W : Set S) →
      ∃ i : OrderDual I, (ι.app i).opensRange ≤ W)
    [∀ i : OrderDual I, QuasiCompact (((ι.app i) ⁻¹ᵁ U).ι)]
    [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))] :
    Functor.IsEquivalence (baseChange s U) := sorry

end AlgebraicGeometry.FinitePresentationIsoOverOpen
