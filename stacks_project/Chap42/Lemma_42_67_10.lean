/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatBaseChange.Limit

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

/- Lemma 42.67.10 (1): cycles of a quasi-compact finite-type scheme after directed affine
limiting base change are the colimit of its stage cycle groups. -/
@[stacks 0FVQ] #check (AlgebraicGeometry.ChowLimit.cycleCocone_isColimit :
  ∀ {I : Type u} [Preorder I] {S : Scheme.{u}} [hS_catenary : UniversallyCatenary S]
    (D : OrderDual I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const (OrderDual I)).obj S)
    (δ : S → ℤ) [hδ : IsDimensionFunction δ]
    [hD_catenary : ∀ index : OrderDual I, UniversallyCatenary (D.obj index)]
    [hD_dimension : ∀ index : I, IsDimensionFunction (ChowLimit.stageDimension D t δ index)]
    [hstage_flat : ∀ index : I, Flat (ChowLimit.stageMap D t index)]
    (X : Over S) [Scheme.Hom.FiniteType X.hom] (k : ℤ)
    [htransition_flat : ∀ (first second : I) (h : first ≤ second),
      Flat (D.map (homOfLE h))]
    (htransition : ∀ (first second : I) (h : first ≤ second),
      @Scheme.Hom.IsDimensionFunctionCompatible
        (D.obj (OrderDual.toDual first)) (D.obj (OrderDual.toDual second))
        (hD_catenary _) (hD_catenary _) (D.map (homOfLE h)) (htransition_flat first second h)
        (ChowLimit.stageDimension D t δ first) (hD_dimension first)
        (ChowLimit.stageDimension D t δ second) (hD_dimension second) 0)
    (c : Cone D) (g : c.pt ⟶ S) [UniversallyCatenary c.pt] [Flat g]
    (δ' : c.pt → ℤ) [IsDimensionFunction δ']
    (hπ : c.π ≫ t = (Functor.const (OrderDual I)).map g)
    [Nonempty I] [IsDirected I (· ≤ ·)] (hc : IsLimit c)
    [∀ index : I, IsAffineHom (ChowLimit.stageMap D t index)]
    (hcompat : g.IsDimensionFunctionCompatible δ δ' 0)
    (hstage : ∀ index : I,
      @Scheme.Hom.IsDimensionFunctionCompatible S (D.obj (OrderDual.toDual index))
        hS_catenary (hD_catenary _) (ChowLimit.stageMap D t index) (hstage_flat index)
        δ hδ (ChowLimit.stageDimension D t δ index) (hD_dimension index) 0) [CompactSpace X.left],
    Nonempty (IsColimit
      (ChowLimit.limitCycleCocone D t δ X k htransition c g δ' hπ hc hcompat hstage)))

/- Lemma 42.67.10 (2): Chow groups of a quasi-compact finite-type scheme after directed
affine limiting base change are the colimit of its stage Chow groups. -/
@[stacks 0FVQ] #check (AlgebraicGeometry.ChowLimit.chowCocone_isColimit :
  ∀ {I : Type u} [Preorder I] {S : Scheme.{u}} [hS_catenary : UniversallyCatenary S]
    (D : OrderDual I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const (OrderDual I)).obj S)
    (δ : S → ℤ) [hδ : IsDimensionFunction δ]
    [hD_catenary : ∀ index : OrderDual I, UniversallyCatenary (D.obj index)]
    [hD_dimension : ∀ index : I, IsDimensionFunction (ChowLimit.stageDimension D t δ index)]
    [hstage_flat : ∀ index : I, Flat (ChowLimit.stageMap D t index)]
    (X : Over S) [Scheme.Hom.FiniteType X.hom] (k : ℤ)
    [htransition_flat : ∀ (first second : I) (h : first ≤ second),
      Flat (D.map (homOfLE h))]
    (htransition : ∀ (first second : I) (h : first ≤ second),
      @Scheme.Hom.IsDimensionFunctionCompatible
        (D.obj (OrderDual.toDual first)) (D.obj (OrderDual.toDual second))
        (hD_catenary _) (hD_catenary _) (D.map (homOfLE h)) (htransition_flat first second h)
        (ChowLimit.stageDimension D t δ first) (hD_dimension first)
        (ChowLimit.stageDimension D t δ second) (hD_dimension second) 0)
    (c : Cone D) (g : c.pt ⟶ S) [UniversallyCatenary c.pt] [Flat g]
    (δ' : c.pt → ℤ) [IsDimensionFunction δ']
    (hπ : c.π ≫ t = (Functor.const (OrderDual I)).map g)
    [Nonempty I] [IsDirected I (· ≤ ·)] (hc : IsLimit c)
    [∀ index : I, IsAffineHom (ChowLimit.stageMap D t index)]
    (hcompat : g.IsDimensionFunctionCompatible δ δ' 0)
    (hstage : ∀ index : I,
      @Scheme.Hom.IsDimensionFunctionCompatible S (D.obj (OrderDual.toDual index))
        hS_catenary (hD_catenary _) (ChowLimit.stageMap D t index) (hstage_flat index)
        δ hδ (ChowLimit.stageDimension D t δ index) (hD_dimension index) 0) [CompactSpace X.left],
    Nonempty (IsColimit
      (ChowLimit.limitChowCocone D t δ X k htransition c g δ' hπ hc hcompat hstage)))
