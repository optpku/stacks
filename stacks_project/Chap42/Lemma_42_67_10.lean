module

import StacksCheckRecall
public import stacks_project.Chap42.Lemma_42_67_10_Continuity

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ChowLimit

variable {I : Type u} [Preorder I] [hI_nonempty : Nonempty I]
variable [hI_directed : IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} [hS_catenary : UniversallyCatenary S]
variable (D : OrderDual I ⥤ Scheme.{u})
variable (t : D ⟶ (Functor.const (OrderDual I)).obj S)
variable (c : Cone D) (hc : IsLimit c)
variable (g : c.pt ⟶ S) [hc_catenary : UniversallyCatenary c.pt] [hg_flat : Flat g]
variable (hπ : c.π ≫ t = (Functor.const (OrderDual I)).map g)
variable (δ : S → ℤ) [hδ : IsDimensionFunction δ]
variable (δ' : c.pt → ℤ) [hδ' : IsDimensionFunction δ']
variable [hD_catenary : ∀ i : OrderDual I, UniversallyCatenary (D.obj i)]
variable [hD_dimension : ∀ i : I, IsDimensionFunction (stageDimension D t δ i)]
variable [hD_affine : ∀ i : I, IsAffineHom (stageMap D t i)]
variable [hstage_flat : ∀ i : I, Flat (stageMap D t i)]
variable [hleg_flat : ∀ i : I, Flat (coneMap D c i)]
variable [htransition_flat : ∀ (i j : I) (h : i ≤ j), Flat (D.map (homOfLE h))]
variable (hcompat : @Scheme.Hom.IsDimensionFunctionCompatible S c.pt
  hS_catenary hc_catenary g hg_flat δ hδ δ' hδ' 0)
variable (hstage : ∀ i : I,
  @Scheme.Hom.IsDimensionFunctionCompatible S (D.obj (OrderDual.toDual i))
    hS_catenary (hD_catenary _) (stageMap D t i) (hstage_flat i)
    δ hδ (stageDimension D t δ i) (hD_dimension i) 0)
variable (hleg : ∀ i : I,
  @Scheme.Hom.IsDimensionFunctionCompatible (D.obj (OrderDual.toDual i)) c.pt
    (hD_catenary _) hc_catenary (coneMap D c i) (hleg_flat i)
    (stageDimension D t δ i) (hD_dimension i) δ' hδ' 0)
variable (htransition : ∀ (i j : I) (h : i ≤ j),
  @Scheme.Hom.IsDimensionFunctionCompatible
    (D.obj (OrderDual.toDual i)) (D.obj (OrderDual.toDual j))
    (hD_catenary _) (hD_catenary _) (D.map (homOfLE h)) (htransition_flat i j h)
    (stageDimension D t δ i) (hD_dimension i)
    (stageDimension D t δ j) (hD_dimension j) 0)
variable (X : Over S) [hX_compact : CompactSpace X.left]
variable [hX_finite : Scheme.Hom.FiniteType X.hom]
variable (k : ℤ)

include hc hcompat hstage hD_affine hI_nonempty hI_directed hX_compact

/-- Lemma 42.67.10 (1): the canonical cocone from the filtered system of degree-`k`
cycle groups of the base changes `X_i` to the cycle group of `X'` is colimiting. -/
@[stacks 0FVQ]
theorem cycleCocone_isColimit : Nonempty (IsColimit
    (cycleCocone D t δ X k htransition c g δ' hπ hleg)) := sorry

/-- Lemma 42.67.10 (2): the canonical cocone from the filtered system of degree-`k`
Chow groups of the base changes `X_i` to the Chow group of `X'` is colimiting. -/
@[stacks 0FVQ]
theorem chowCocone_isColimit : Nonempty (IsColimit
    (chowCocone D t δ X k htransition c g δ' hπ hleg)) := sorry

/-- The canonical comparison from the filtered colimit of cycle groups to the cycle group
on `X'` is an isomorphism. -/
theorem cycleComparison_isIso :
    IsIso (cycleComparison D t δ X k htransition c g δ' hπ hleg) := sorry

/-- The canonical comparison from the filtered colimit of Chow groups to the Chow group
on `X'` is an isomorphism. -/
theorem chowComparison_isIso :
    IsIso (chowComparison D t δ X k htransition c g δ' hπ hleg) := sorry

end AlgebraicGeometry.ChowLimit
