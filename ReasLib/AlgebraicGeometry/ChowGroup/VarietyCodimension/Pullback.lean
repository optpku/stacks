/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Reindex
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Intersection
public import ReasLib.AlgebraicGeometry.CycleGroup.ExteriorProduct
public import ReasLib.AlgebraicGeometry.CycleGroup.ExteriorProduct.Intersection
public import ReasLib.AlgebraicGeometry.CycleGroup.Fundamental
public import ReasLib.AlgebraicGeometry.CycleGroup.Intersection
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Graph
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Product
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Product.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Product
public import ReasLib.AlgebraicGeometry.Scheme.Variety.ProjectiveProper
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Properties

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.VarietyCodimension

/-- The codimension-`p` Chow group of an irreducible variety. -/
abbrev Class {k : Type u} [Field k] (X : SchemeOverField k) [Variety X]
    (p : ℤ) : Type u :=
  RelativeChow (fun _ ↦ (0 : ℤ)) X ((X.dimension : ℤ) - p)

/-- The graph of a morphism of varieties, viewed inside their product. -/
noncomputable abbrev graph {k : Type u} [Field k]
    {X Y : SchemeOverField k} (f : X ⟶ Y) : X.left ⟶ (X ⨯ Y).left :=
  Over.graph f ≫ (Over.prodLeftIsoPullback X Y).inv

/-- The graph has the identity and `f` as its two projections. -/
theorem graph_spec {k : Type u} [Field k]
    {X Y : SchemeOverField k} (f : X ⟶ Y) :
    graph f ≫ (prod.fst : X ⨯ Y ⟶ X).left = 𝟙 X.left ∧
      graph f ≫ (prod.snd : X ⨯ Y ⟶ Y).left = f.left := sorry

/-- The graph cycle has the dimension of its source variety. -/
theorem graphCycle_mem_dimensionSubgroup {k : Type u} [Field k]
    {X Y : SchemeOverField k} [ProjectiveVariety X] [ProjectiveVariety Y]
    [IsAlgClosed k] (f : X ⟶ Y) :
    AlgebraicCycle.map (graph f)
        (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
        ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
        (@AlgebraicCycle.fundamental X.left
          (@LocallyOfFiniteType.isLocallyNoetherian _ _ X.hom inferInstance
            (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
              (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
          (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
          (X.dimension : ℤ)) ∈
      AlgebraicCycle.dimensionSubgroup
        ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
        (X.dimension : ℤ) := sorry

/-- The cycle of the graph of a morphism of projective varieties. -/
noncomputable def graphCycle {k : Type u} [Field k]
    {X Y : SchemeOverField k} [ProjectiveVariety X] [ProjectiveVariety Y]
    [IsAlgClosed k] (f : X ⟶ Y) :
    CycleGroup (X ⨯ Y).left
      ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
      (X.dimension : ℤ) :=
  ⟨AlgebraicCycle.map (graph f)
      (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
      ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
      (@AlgebraicCycle.fundamental X.left
        (@LocallyOfFiniteType.isLocallyNoetherian _ _ X.hom inferInstance
          (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
            (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
        (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
        (X.dimension : ℤ)),
    graphCycle_mem_dimensionSubgroup f⟩

/-- Forgetting the grading of the graph cycle gives the pushforward of the
fundamental cycle along the graph. -/
theorem toAlgebraicCycle_graphCycle {k : Type u} [Field k]
    {X Y : SchemeOverField k} [ProjectiveVariety X] [ProjectiveVariety Y]
    [IsAlgClosed k] (f : X ⟶ Y) :
    CycleGroup.toAlgebraicCycle
        ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
        (X.dimension : ℤ) (graphCycle f) =
      AlgebraicCycle.map (graph f)
        (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
        ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
        (@AlgebraicCycle.fundamental X.left
          (@LocallyOfFiniteType.isLocallyNoetherian _ _ X.hom inferInstance
            (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
              (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
          (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
          (X.dimension : ℤ)) := sorry

/-- The dimension degree produced by graph intersection before its codimension
regrading. -/
def pullbackCycleDegree {k : Type u} [Field k]
    (X Y : SchemeOverField k) [ProjectiveVariety X] [ProjectiveVariety Y]
    [IsAlgClosed k] (p : ℤ) : ℤ :=
  (X.dimension : ℤ) + ((X.dimension : ℤ) + ((Y.dimension : ℤ) - p)) -
    ((X ⨯ Y).dimension : ℤ)

/-- Graph intersection has the degree corresponding to codimension `p` on `X`. -/
theorem pullbackCycleDegree_eq {k : Type u} [Field k]
    (X Y : SchemeOverField k) [ProjectiveVariety X] [ProjectiveVariety Y]
    [IsAlgClosed k] (p : ℤ) :
    pullbackCycleDegree X Y p = (X.dimension : ℤ) - p := sorry

/-- A moved exterior representative suitable for intersection with the graph. -/
structure GraphRepresentative {k : Type u} [Field k]
    {X Y : SchemeOverField k} [ProjectiveVariety X] [ProjectiveVariety Y]
    [IsAlgClosed k] (f : X ⟶ Y) (p : ℤ) (beta : Class Y p)
    (gamma : CycleGroup (X ⨯ Y).left
      ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
      ((X.dimension : ℤ) + ((Y.dimension : ℤ) - p))) : Prop where
  rationallyEquivalent :
    @RationalEquivalence.RationallyEquivalent (X ⨯ Y).left
      (@LocallyOfFiniteType.isLocallyNoetherian _ _ (X ⨯ Y).hom inferInstance
        (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
          (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
      ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
      inferInstance
      ((X.dimension : ℤ) + ((Y.dimension : ℤ) - p)) gamma
      (CycleGroup.exteriorProductPairing X Y (X.dimension : ℤ)
        ((Y.dimension : ℤ) - p)
        (@CycleGroup.fundamental X.left
          (@LocallyOfFiniteType.isLocallyNoetherian _ _ X.hom inferInstance
            (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
              (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
          (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
          (X.dimension : ℤ)) (Quotient.out beta))
  intersectsGraph :
    AlgebraicCycle.IntersectProperly
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
        (X.dimension : ℤ) (graphCycle f))
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
        ((X.dimension : ℤ) + ((Y.dimension : ℤ) - p)) gamma)

/-- Construct a graph-suitable representative from its two defining properties. -/
def GraphRepresentative.ofProperties {k : Type u} [Field k]
    {X Y : SchemeOverField k} [ProjectiveVariety X] [ProjectiveVariety Y]
    [IsAlgClosed k] (f : X ⟶ Y) (p : ℤ) (beta : Class Y p)
    (gamma : CycleGroup (X ⨯ Y).left
      ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
      ((X.dimension : ℤ) + ((Y.dimension : ℤ) - p)))
    (h_rational : @RationalEquivalence.RationallyEquivalent (X ⨯ Y).left
      (@LocallyOfFiniteType.isLocallyNoetherian _ _ (X ⨯ Y).hom inferInstance
        (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
          (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
      ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
      inferInstance
      ((X.dimension : ℤ) + ((Y.dimension : ℤ) - p)) gamma
      (CycleGroup.exteriorProductPairing X Y (X.dimension : ℤ)
        ((Y.dimension : ℤ) - p)
        (@CycleGroup.fundamental X.left
          (@LocallyOfFiniteType.isLocallyNoetherian _ _ X.hom inferInstance
            (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
              (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
          (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
          (X.dimension : ℤ)) (Quotient.out beta)))
    (h_proper : AlgebraicCycle.IntersectProperly
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
        (X.dimension : ℤ) (graphCycle f))
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
        ((X.dimension : ℤ) + ((Y.dimension : ℤ) - p)) gamma)) :
    GraphRepresentative f p beta gamma :=
  ⟨h_rational, h_proper⟩

/-- Every Chow class admits an exterior representative meeting the graph properly. -/
theorem exists_graphRepresentative {k : Type u} [Field k]
    {X Y : SchemeOverField k} [ProjectiveVariety X] [ProjectiveVariety Y]
    [Scheme.Regular X.left] [Scheme.Regular Y.left] [IsAlgClosed k]
    (f : X ⟶ Y) (p : ℤ) (beta : Class Y p) :
    ∃ gamma : CycleGroup (X ⨯ Y).left
        ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
        ((X.dimension : ℤ) + ((Y.dimension : ℤ) - p)),
      GraphRepresentative f p beta gamma := sorry

/-- Intersect a moved exterior representative with the graph, push it to `X`, and
regrade the resulting Chow class by codimension. -/
noncomputable def graphIntersectionClass {k : Type u} [Field k]
    {X Y : SchemeOverField k} [ProjectiveVariety X] [ProjectiveVariety Y]
    [Scheme.Regular X.left] [Scheme.Regular Y.left] [IsAlgClosed k]
    (f : X ⟶ Y) (p : ℤ) (beta : Class Y p)
    (gamma : CycleGroup (X ⨯ Y).left
      ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
      ((X.dimension : ℤ) + ((Y.dimension : ℤ) - p)))
    (hgamma : GraphRepresentative f p beta gamma)
    (hdegree : pullbackCycleDegree X Y p = (X.dimension : ℤ) - p) :
    Class X p :=
  ChowGroup.reindex (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ))) hdegree
    (@chowClass X.left
      (@LocallyOfFiniteType.isLocallyNoetherian _ _ X.hom inferInstance
        (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
          (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
      (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ))) inferInstance
      (pullbackCycleDegree X Y p)
      (@CycleGroup.mapHom (X ⨯ Y).left X.left
        (prod.fst : X ⨯ Y ⟶ X).left
        (by
          -- Local instance justification (proof-local temporary data): properness is needed only to construct this explicit pushforward.
          letI : IsProper (Over.Hom.left (prod.fst : X ⨯ Y ⟶ X)) :=
            SchemeOverField.prodFstIsProper X Y
          exact inferInstance)
        ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
        (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
        (pullbackCycleDegree X Y p)
        (@CycleGroup.intersection k _ (X ⨯ Y) _ (SchemeOverField.regularProdOfRegular X Y)
          (X.dimension : ℤ)
          ((X.dimension : ℤ) + ((Y.dimension : ℤ) - p)) (graphCycle f) gamma
          hgamma.intersectsGraph)))

/-- The graph-intersection class is represented by graph intersection followed by
first-projection pushforward. -/
theorem graphIntersectionClass_spec {k : Type u} [Field k]
    {X Y : SchemeOverField k} [ProjectiveVariety X] [ProjectiveVariety Y]
    [Scheme.Regular X.left] [Scheme.Regular Y.left] [IsAlgClosed k]
    (f : X ⟶ Y) (p : ℤ) (beta : Class Y p)
    (gamma : CycleGroup (X ⨯ Y).left
      ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
      ((X.dimension : ℤ) + ((Y.dimension : ℤ) - p)))
    (hgamma : GraphRepresentative f p beta gamma)
    (hdegree : pullbackCycleDegree X Y p = (X.dimension : ℤ) - p) :
    graphIntersectionClass f p beta gamma hgamma hdegree =
      ChowGroup.reindex (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ))) hdegree
        (@chowClass X.left
          (@LocallyOfFiniteType.isLocallyNoetherian _ _ X.hom inferInstance
            (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
              (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
          (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ))) inferInstance
          (pullbackCycleDegree X Y p)
          (@CycleGroup.mapHom (X ⨯ Y).left X.left
            (prod.fst : X ⨯ Y ⟶ X).left
            (by
              -- Local instance justification (proof-local temporary data): properness is needed only to construct this explicit pushforward.
              letI : IsProper (Over.Hom.left (prod.fst : X ⨯ Y ⟶ X)) :=
                SchemeOverField.prodFstIsProper X Y
              exact inferInstance)
            ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
            (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
            (pullbackCycleDegree X Y p)
            (@CycleGroup.intersection k _ (X ⨯ Y) _ (SchemeOverField.regularProdOfRegular X Y)
              (X.dimension : ℤ)
              ((X.dimension : ℤ) + ((Y.dimension : ℤ) - p)) (graphCycle f) gamma
              hgamma.intersectsGraph))) := sorry

/-- The graph/intersection formula for pullback, with total fallback branches that are
proved unreachable by the moving and dimension theorems. -/
noncomputable def pullbackValue {k : Type u} [Field k]
    {X Y : SchemeOverField k} [ProjectiveVariety X] [ProjectiveVariety Y]
    [Scheme.Regular X.left] [Scheme.Regular Y.left] [IsAlgClosed k]
    (f : X ⟶ Y) (p : ℤ) (beta : Class Y p) : Class X p :=
  @dite (Class X p)
    (pullbackCycleDegree X Y p = (X.dimension : ℤ) - p)
    (Classical.propDecidable _)
    (fun hdegree ↦
      @dite (Class X p)
        (∃ gamma : CycleGroup (X ⨯ Y).left
            ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
            ((X.dimension : ℤ) + ((Y.dimension : ℤ) - p)),
          GraphRepresentative f p beta gamma)
        (Classical.propDecidable _)
        (fun hgamma ↦ graphIntersectionClass f p beta (Classical.choose hgamma)
          (Classical.choose_spec hgamma) hdegree)
        (fun _ ↦ 0))
    (fun _ ↦ 0)

/-- The graph/intersection pullback sends zero to zero. -/
theorem pullbackValue_zero {k : Type u} [Field k]
    {X Y : SchemeOverField k} [ProjectiveVariety X] [ProjectiveVariety Y]
    [Scheme.Regular X.left] [Scheme.Regular Y.left] [IsAlgClosed k]
    (f : X ⟶ Y) (p : ℤ) :
    pullbackValue f p (0 : Class Y p) = 0 := sorry

/-- The graph/intersection pullback is additive. -/
theorem pullbackValue_add {k : Type u} [Field k]
    {X Y : SchemeOverField k} [ProjectiveVariety X] [ProjectiveVariety Y]
    [Scheme.Regular X.left] [Scheme.Regular Y.left] [IsAlgClosed k]
    (f : X ⟶ Y) (p : ℤ) (alpha beta : Class Y p) :
    pullbackValue f p (alpha + beta) =
      pullbackValue f p alpha + pullbackValue f p beta := sorry

/-- Pullback on codimension-graded Chow groups, defined by graph intersection. -/
noncomputable def pullback {k : Type u} [Field k]
    {X Y : SchemeOverField k} [ProjectiveVariety X] [ProjectiveVariety Y]
    [Scheme.Regular X.left] [Scheme.Regular Y.left] [IsAlgClosed k]
    (f : X ⟶ Y) (p : ℤ) : Class Y p →+ Class X p where
  toFun := pullbackValue f p
  map_zero' := pullbackValue_zero f p
  map_add' := pullbackValue_add f p

/-- Pullback is independent of the moved representative and is computed by the
graph/intersection formula. -/
theorem pullback_spec {k : Type u} [Field k]
    {X Y : SchemeOverField k} [ProjectiveVariety X] [ProjectiveVariety Y]
    [Scheme.Regular X.left] [Scheme.Regular Y.left] [IsAlgClosed k]
    (f : X ⟶ Y) (p : ℤ) (beta : Class Y p)
    (gamma : CycleGroup (X ⨯ Y).left
      ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
      ((X.dimension : ℤ) + ((Y.dimension : ℤ) - p)))
    (hgamma : GraphRepresentative f p beta gamma) :
    pullback f p beta = graphIntersectionClass f p beta gamma hgamma
      (pullbackCycleDegree_eq X Y p) := sorry

/-- The codimension-zero fundamental Chow class of a variety. -/
noncomputable def fundamentalClass {k : Type u} [Field k]
    (X : SchemeOverField k) [ProjectiveVariety X] : Class X 0 :=
  @ChowGroup.reindex X.left
    (@LocallyOfFiniteType.isLocallyNoetherian _ _ X.hom inferInstance
      (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
        (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
    (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ))) inferInstance
    (X.dimension : ℤ) ((X.dimension : ℤ) - 0)
    (sub_zero (X.dimension : ℤ)).symm
    (@chowClass X.left
      (@LocallyOfFiniteType.isLocallyNoetherian _ _ X.hom inferInstance
        (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
          (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
      (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ))) inferInstance
      (X.dimension : ℤ)
      (@CycleGroup.fundamental X.left
        (@LocallyOfFiniteType.isLocallyNoetherian _ _ X.hom inferInstance
          (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
            (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
        (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
        (X.dimension : ℤ)))

/-- The codimension-zero class is represented by the fundamental cycle. -/
theorem fundamentalClass_spec {k : Type u} [Field k]
    (X : SchemeOverField k) [ProjectiveVariety X] :
    HEq (fundamentalClass X)
      (@chowClass X.left
        (@LocallyOfFiniteType.isLocallyNoetherian _ _ X.hom inferInstance
          (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
            (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
        (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ))) inferInstance
        (X.dimension : ℤ)
        (@CycleGroup.fundamental X.left
          (@LocallyOfFiniteType.isLocallyNoetherian _ _ X.hom inferInstance
            (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
              (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
          (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
          (X.dimension : ℤ))) := sorry

/-- A Chow class is the intersection product of two classes when it is represented
by the proper intersection of rationally equivalent cycle representatives. -/
inductive IsIntersectionProduct {k : Type u} [Field k]
    (X : SchemeOverField k) [ProjectiveVariety X] [Scheme.Regular X.left]
    (r s t : ℤ)
    (alpha : RelativeChow (fun _ ↦ (0 : ℤ)) X r)
    (beta : RelativeChow (fun _ ↦ (0 : ℤ)) X s)
    (gamma : RelativeChow (fun _ ↦ (0 : ℤ)) X t) : Prop where
  /-- Proper representatives whose intersection represents the asserted product. -/
  | ofCycles
      (leftCycle : CycleGroup X.left
        (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ))) r)
      (rightCycle : CycleGroup X.left
        (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ))) s)
      (hleft : chowClass (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ))) r
        leftCycle = alpha)
      (hright : chowClass (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ))) s
        rightCycle = beta)
      (hproper : AlgebraicCycle.IntersectProperly
        (CycleGroup.toAlgebraicCycle
          (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ))) r leftCycle)
        (CycleGroup.toAlgebraicCycle
          (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ))) s rightCycle))
      (hproduct : HEq
        (chowClass (X.hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
          (r + s - (X.dimension : ℤ))
          (CycleGroup.intersection X r s leftCycle rightCycle hproper)) gamma) :
      IsIntersectionProduct X r s t alpha beta gamma

/-- Every pair of codimension-graded Chow classes has an intersection product. -/
theorem exists_intersectionProduct {k : Type u} [Field k]
    (X : SchemeOverField k) [ProjectiveVariety X] [Scheme.Regular X.left]
    [IsAlgClosed k] (p q : ℤ) (alpha : Class X p) (beta : Class X q) :
    ∃ gamma : Class X (p + q),
      IsIntersectionProduct X ((X.dimension : ℤ) - p)
        ((X.dimension : ℤ) - q) ((X.dimension : ℤ) - (p + q))
        alpha beta gamma := sorry

/-- The Chow intersection class represented by proper intersections is unique. -/
theorem intersectionProduct_unique {k : Type u} [Field k]
    (X : SchemeOverField k) [ProjectiveVariety X] [Scheme.Regular X.left]
    [IsAlgClosed k] (r s t : ℤ)
    (alpha : RelativeChow (fun _ ↦ (0 : ℤ)) X r)
    (beta : RelativeChow (fun _ ↦ (0 : ℤ)) X s)
    (gamma delta : RelativeChow (fun _ ↦ (0 : ℤ)) X t)
    (hgamma : IsIntersectionProduct X r s t alpha beta gamma)
    (hdelta : IsIntersectionProduct X r s t alpha beta delta) :
    gamma = delta := sorry

/-- The graph pullback is a graded ring map when it preserves the fundamental class
and all intersection products. -/
structure IsGradedRingMap {k : Type u} [Field k]
    {X Y : SchemeOverField k} [ProjectiveVariety X] [ProjectiveVariety Y]
    [Scheme.Regular X.left] [Scheme.Regular Y.left] [IsAlgClosed k]
    (f : X ⟶ Y) : Prop where
  map_one : pullback f 0 (fundamentalClass Y) = fundamentalClass X
  map_mul : ∀ (p q : ℤ) (alpha : Class Y p) (beta : Class Y q)
      (gamma : Class Y (p + q)) (delta : Class X (p + q)),
    IsIntersectionProduct Y ((Y.dimension : ℤ) - p) ((Y.dimension : ℤ) - q)
        ((Y.dimension : ℤ) - (p + q)) alpha beta gamma →
      IsIntersectionProduct X ((X.dimension : ℤ) - p) ((X.dimension : ℤ) - q)
        ((X.dimension : ℤ) - (p + q))
        (pullback f p alpha) (pullback f q beta) delta →
      pullback f (p + q) gamma = delta

/-- Build the graded-ring-map property from preservation of one and products. -/
def IsGradedRingMap.ofProperties {k : Type u} [Field k]
    {X Y : SchemeOverField k} [ProjectiveVariety X] [ProjectiveVariety Y]
    [Scheme.Regular X.left] [Scheme.Regular Y.left] [IsAlgClosed k]
    (f : X ⟶ Y)
    (h_one : pullback f 0 (fundamentalClass Y) = fundamentalClass X)
    (h_mul : ∀ (p q : ℤ) (alpha : Class Y p) (beta : Class Y q)
      (gamma : Class Y (p + q)) (delta : Class X (p + q)),
      IsIntersectionProduct Y ((Y.dimension : ℤ) - p) ((Y.dimension : ℤ) - q)
          ((Y.dimension : ℤ) - (p + q)) alpha beta gamma →
        IsIntersectionProduct X ((X.dimension : ℤ) - p) ((X.dimension : ℤ) - q)
          ((X.dimension : ℤ) - (p + q))
          (pullback f p alpha) (pullback f q beta) delta →
        pullback f (p + q) gamma = delta) :
    IsGradedRingMap f :=
  ⟨h_one, h_mul⟩

/-- Graph pullback on codimension-graded Chow groups of regular projective varieties
preserves the fundamental class and intersection products. -/
theorem pullback_isGradedRingMap
    {k : Type u} [Field k]
    {X Y : SchemeOverField k} [ProjectiveVariety X] [ProjectiveVariety Y]
    [Scheme.Regular X.left] [Scheme.Regular Y.left] [IsAlgClosed k]
    (f : X ⟶ Y) : IsGradedRingMap f := sorry

/-- Graph pullback on codimension-graded Chow groups is contravariantly functorial. -/
theorem pullback_comp
    {k : Type u} [Field k]
    {X Y Z : SchemeOverField k}
    [ProjectiveVariety X] [ProjectiveVariety Y] [ProjectiveVariety Z]
    [Scheme.Regular X.left] [Scheme.Regular Y.left] [Scheme.Regular Z.left]
    [IsAlgClosed k] (f : X ⟶ Y) (g : Y ⟶ Z) (p : ℤ)
    (alpha : Class Z p) :
    pullback (f ≫ g) p alpha = pullback f p (pullback g p alpha) := sorry

/-- Graph pullback and proper pushforward on Chow groups satisfy the projection formula. -/
theorem pullback_projectionFormula
    {k : Type u} [Field k]
    {X Y : SchemeOverField k} [ProjectiveVariety X] [ProjectiveVariety Y]
    [Scheme.Regular X.left] [Scheme.Regular Y.left] [IsAlgClosed k]
    (f : X ⟶ Y) (n q : ℤ)
    (alpha : RelativeChow (fun _ ↦ (0 : ℤ)) X n) (beta : Class Y q)
    (leftProduct : RelativeChow (fun _ ↦ (0 : ℤ)) Y (n - q))
    (rightProduct : RelativeChow (fun _ ↦ (0 : ℤ)) X (n - q))
    (hleft : IsIntersectionProduct Y n ((Y.dimension : ℤ) - q) (n - q)
      (ChowGroup.map (fun _ ↦ (0 : ℤ)) X Y f n alpha) beta leftProduct)
    (hright : IsIntersectionProduct X n ((X.dimension : ℤ) - q) (n - q)
      alpha (pullback f q beta) rightProduct) :
    leftProduct =
      ChowGroup.map (fun _ ↦ (0 : ℤ)) X Y f (n - q) rightProduct := sorry

/-- For a flat morphism of regular projective varieties, graph pullback agrees with flat
pullback after transporting between the codimension and dimension gradings. -/
theorem pullback_eq_flatPullback
    {k : Type u} [Field k]
    {X Y : SchemeOverField k} [ProjectiveVariety X] [ProjectiveVariety Y]
    [Scheme.Regular X.left] [Scheme.Regular Y.left] [IsAlgClosed k]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (p : ℤ) (alpha : Class Y p) :
    HEq (pullback f p alpha)
      (ChowGroup.flatPullback (fun _ ↦ (0 : ℤ)) X Y f r
        ((Y.dimension : ℤ) - p) alpha) := sorry

end AlgebraicGeometry.ChowGroup.VarietyCodimension
