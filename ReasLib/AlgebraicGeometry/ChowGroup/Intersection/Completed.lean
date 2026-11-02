/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Clopen
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Smooth
public import ReasLib.AlgebraicGeometry.ChowGroup.Intersection.Total
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Operations

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.SchemeOverField AlgebraicGeometry.Scheme.Hom
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.DimensionCompleted

variable {k : Type u} [Field k]

/-- Chow homology of a smooth scheme of dimension `d` vanishes outside degrees `0,…,d`. -/
theorem relativeChow_eq_zero_of_degree_outside (X : SchemeOverField k)
    [Smooth X.hom] (d : ℕ) [RelativeDimension X.hom d] (n : ℤ)
    (hn : n < 0 ∨ (d : ℤ) < n) (a : RelativeChow (fun _ ↦ 0) X n) : a = 0 := sorry

/-- The canonical integral intersection pairing on dimension-completed Chow homology. -/
def smoothIntersectionProduct (X : SchemeOverField k) [Smooth X.hom] :
    DimensionCompleted X →+ DimensionCompleted X →+ DimensionCompleted X where
  toFun a :=
    { toFun := fun b d ↦ Total.smoothIntersectionProductOfDimension
        (dimensionComponent X d) d (a d) (b d)
      map_zero' := funext fun d ↦ map_zero
        (Total.smoothIntersectionProductOfDimension (dimensionComponent X d) d (a d))
      map_add' b c := funext fun d ↦ map_add
        (Total.smoothIntersectionProductOfDimension (dimensionComponent X d) d (a d))
        (b d) (c d) }
  map_zero' := by
    apply AddMonoidHom.ext
    intro b
    funext d
    exact congrArg (fun h ↦ h (b d))
      (map_zero (Total.smoothIntersectionProductOfDimension (dimensionComponent X d) d))
  map_add' a b := by
    apply AddMonoidHom.ext
    intro c
    funext d
    exact congrArg (fun h ↦ h (c d))
      (map_add (Total.smoothIntersectionProductOfDimension (dimensionComponent X d) d)
        (a d) (b d))

/-- Evaluation of a total Chow class in a fixed homogeneous degree. -/
def degreeEvaluation (X : SchemeOverField k) [LocallyOfFiniteType X.hom] (n : ℤ) :
    Total (fun _ ↦ 0) X →+ RelativeChow (fun _ ↦ 0) X n where
  toFun a := a n
  map_zero' := rfl
  map_add' _ _ := rfl

variable {X Y : SchemeOverField k} [Smooth X.hom] [Smooth Y.hom]

/-- Within the source dimension-`d` component, the inverse image of target dimension `e`. -/
def sourceTargetDimensionLocus (f : X ⟶ Y) (d e : ℕ) :
    (dimensionComponent X d).left.Opens :=
  (dimensionComponentι X d ≫ f).left ⁻¹ᵁ smoothRelativeDimensionLocus Y.hom e

/-- The source of the restriction to prescribed source and target dimensions. -/
abbrev sourceTargetDimensionComponent (f : X ⟶ Y) (d e : ℕ) :=
  BivariantClass.ComponentRestriction.over (dimensionComponent X d) (sourceTargetDimensionLocus f d e)

/-- The morphism restricted to prescribed source and target dimension components. -/
def sourceTargetDimensionMap (f : X ⟶ Y) (d e : ℕ) :
    sourceTargetDimensionComponent f d e ⟶ dimensionComponent Y e :=
  BivariantClass.ComponentRestriction.hom (dimensionComponentι X d ≫ f)
    (sourceTargetDimensionLocus f d e) (smoothRelativeDimensionLocus Y.hom e) le_rfl

/-- Restricting a source dimension component to any target dimension locus preserves its dimension. -/
theorem sourceTargetDimensionLocus_relativeDimension (f : X ⟶ Y) (d e : ℕ) :
    RelativeDimension (sourceTargetDimensionComponent f d e).hom d := by
  change RelativeDimension
    ((sourceTargetDimensionLocus f d e).ι ≫ (dimensionComponent X d).hom) d
  simpa using
    (relativeDimension_comp_of_flat (d := 0) (e := d)
      (sourceTargetDimensionLocus f d e).ι (dimensionComponent X d).hom)

private theorem sourceTarget_closed (f : X ⟶ Y) (d e : ℕ) :
    IsClosed (sourceTargetDimensionLocus f d e : Set (dimensionComponent X d).left) :=
  (smoothRelativeDimensionLocus_isClopen Y.hom e).isClosed.preimage
    (dimensionComponentι X d ≫ f).left.continuous

private theorem sourceTarget_disjoint (f : X ⟶ Y) (d : ℕ) :
    Pairwise fun e e' ↦ Disjoint
      (sourceTargetDimensionLocus f d e : Set (dimensionComponent X d).left)
      (sourceTargetDimensionLocus f d e' : Set (dimensionComponent X d).left) := by
  intro e e' h
  exact (smoothRelativeDimensionLocus_pairwiseDisjoint Y.hom h).preimage _

private theorem sourceTarget_cover (f : X ⟶ Y) (d : ℕ) :
    iSup (sourceTargetDimensionLocus f d) = ⊤ := by
  change (⨆ e, (dimensionComponentι X d ≫ f).left ⁻¹ᵁ
    smoothRelativeDimensionLocus Y.hom e) = ⊤
  rw [← Scheme.Hom.preimage_iSup, smoothRelativeDimensionLocus_iSup,
    Scheme.Hom.preimage_top]

private def restrictedCycleMap {A B : SchemeOverField k}
    [LocallyOfFiniteType A.hom] [LocallyOfFiniteType B.hom]
    (g : A ⟶ B) [IsProper g.left] (V : B.left.Opens) (n : ℤ) :
    CycleGroup A.left (A.hom.relativeDimensionFunction (fun _ ↦ 0)) n →+
      Clopen.cycles (fun _ ↦ 0) B V n :=
  (CycleGroup.mapHom (g.left ∣_ V)
    (((g.left ⁻¹ᵁ V).ι ≫ A.hom).relativeDimensionFunction (fun _ ↦ 0))
    ((V.ι ≫ B.hom).relativeDimensionFunction (fun _ ↦ 0)) n).comp
      ((AddEquiv.cast (by simp : n + (0 : ℕ) = n)).toAddMonoidHom.comp
        (@CycleGroup.flatPullback _ _ (fun _ ↦ 0) _
          (BivariantClass.ComponentRestriction.over A (g.left ⁻¹ᵁ V)) A
          (inferInstanceAs (LocallyOfFiniteType ((g.left ⁻¹ᵁ V).ι ≫ A.hom))) _
          (BivariantClass.ComponentRestriction.ι A (g.left ⁻¹ᵁ V)) 0
          (inferInstanceAs (Flat (g.left ⁻¹ᵁ V).ι))
          (inferInstanceAs (RelativeDimension (g.left ⁻¹ᵁ V).ι 0)) n))

/-- Cycles on a source dimension component, restricted over a target dimension component
and pushed forward into that target component. -/
@[no_expose] def componentPushCycles (f : X ⟶ Y) [IsProper f.left]
    (e : ℕ) (n : ℤ) (d : ℕ) :
    CycleGroup (dimensionComponent X d).left
      ((dimensionComponent X d).hom.relativeDimensionFunction (fun _ ↦ 0)) n →+
    CycleGroup (dimensionComponent Y e).left
      ((dimensionComponent Y e).hom.relativeDimensionFunction (fun _ ↦ 0)) n :=
  @restrictedCycleMap k _ (dimensionComponent X d) Y _ _
    (dimensionComponentι X d ≫ f)
    (inferInstanceAs (IsProper ((dimensionComponentι X d).left ≫ f.left)))
    (smoothRelativeDimensionLocus Y.hom e) n

/-- Proper images of cycles carried by the source dimension components form a locally finite family. -/
theorem properComponentImages_locallyFinite (f : X ⟶ Y) [IsProper f.left]
    (e : ℕ) (n : ℤ)
    (a : ∀ d, CycleGroup (dimensionComponent X d).left
      ((dimensionComponent X d).hom.relativeDimensionFunction (fun _ ↦ 0)) n) :
    LocallyFinite fun d ↦
      (CycleGroup.toAlgebraicCycle
        ((dimensionComponent Y e).hom.relativeDimensionFunction (fun _ ↦ 0)) n
        (componentPushCycles f e n d (a d))).support := sorry

/-- The locally finite cycle sum computing pushforward into a homogeneous target component. -/
def mapDegreeCycles (f : X ⟶ Y) [IsProper f.left] (e : ℕ) (n : ℤ)
    (a : ∀ d, CycleGroup (dimensionComponent X d).left
      ((dimensionComponent X d).hom.relativeDimensionFunction (fun _ ↦ 0)) n) :
    CycleGroup (dimensionComponent Y e).left
      ((dimensionComponent Y e).hom.relativeDimensionFunction (fun _ ↦ 0)) n :=
  CycleGroup.locallyFiniteSum
    ((dimensionComponent Y e).hom.relativeDimensionFunction (fun _ ↦ 0)) n
    (fun d ↦ componentPushCycles f e n d (a d))
    (properComponentImages_locallyFinite f e n a)

/-- The cycle sum defining proper pushforward preserves rational boundaries. -/
theorem mapDegree_mem_boundaries (f : X ⟶ Y) [IsProper f.left] (e : ℕ) (n : ℤ)
    (a : ∀ d, CycleGroup (dimensionComponent X d).left
      ((dimensionComponent X d).hom.relativeDimensionFunction (fun _ ↦ 0)) n)
    (ha : ∀ d, a d ∈ @RationalEquivalence.boundaries (dimensionComponent X d).left
      (LocallyOfFiniteType.isLocallyNoetherian (dimensionComponent X d).hom)
      ((dimensionComponent X d).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n) :
    mapDegreeCycles f e n a ∈ @RationalEquivalence.boundaries (dimensionComponent Y e).left
      (LocallyOfFiniteType.isLocallyNoetherian (dimensionComponent Y e).hom)
      ((dimensionComponent Y e).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n := sorry

/-- The homogeneous Chow class of the locally finite proper image of a family of cycles. -/
def mapDegreeCycleClass (f : X ⟶ Y) [IsProper f.left] (e : ℕ) (n : ℤ)
    (a : ∀ d, CycleGroup (dimensionComponent X d).left
      ((dimensionComponent X d).hom.relativeDimensionFunction (fun _ ↦ 0)) n) :
    RelativeChow (fun _ ↦ 0) (dimensionComponent Y e) n :=
  @chowClass (dimensionComponent Y e).left
    (LocallyOfFiniteType.isLocallyNoetherian (dimensionComponent Y e).hom)
    ((dimensionComponent Y e).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n
    (mapDegreeCycles f e n a)

/-- Homogeneous proper-image assembly sends zero cycles to the zero Chow class. -/
theorem mapDegree_zero (f : X ⟶ Y) [IsProper f.left] (e : ℕ) (n : ℤ) :
    mapDegreeCycleClass f e n 0 = 0 := by
  have hzero : mapDegreeCycles f e n (fun _ ↦ 0) = 0 := by
    unfold mapDegreeCycles
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro y
    change ∑ᶠ d, CycleGroup.toAlgebraicCycle
        ((dimensionComponent Y e).hom.relativeDimensionFunction (fun _ ↦ 0)) n
        (componentPushCycles f e n d 0) y = 0
    have hz (d : ℕ) : CycleGroup.toAlgebraicCycle
        ((dimensionComponent Y e).hom.relativeDimensionFunction (fun _ ↦ 0)) n
        (componentPushCycles f e n d 0) y = 0 := by
      rw [(componentPushCycles f e n d).map_zero]
      rfl
    simp_rw [hz]
    exact finsum_zero
  have hzero' : mapDegreeCycles f e n 0 = 0 := by
    exact hzero
  unfold mapDegreeCycleClass
  rw [hzero', map_zero]

/-- Homogeneous proper-image assembly is additive on Chow classes of cycles. -/
theorem mapDegree_add (f : X ⟶ Y) [IsProper f.left] (e : ℕ) (n : ℤ)
    (a b : ∀ d, CycleGroup (dimensionComponent X d).left
      ((dimensionComponent X d).hom.relativeDimensionFunction (fun _ ↦ 0)) n) :
    mapDegreeCycleClass f e n (a + b) =
      mapDegreeCycleClass f e n a + mapDegreeCycleClass f e n b := by
  have hadd : mapDegreeCycles f e n (a + b) =
      mapDegreeCycles f e n a + mapDegreeCycles f e n b := by
    unfold mapDegreeCycles
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro y
    change (∑ᶠ d, CycleGroup.toAlgebraicCycle
        ((dimensionComponent Y e).hom.relativeDimensionFunction (fun _ ↦ 0)) n
        (componentPushCycles f e n d ((a + b) d)) y) =
      (∑ᶠ d, CycleGroup.toAlgebraicCycle
        ((dimensionComponent Y e).hom.relativeDimensionFunction (fun _ ↦ 0)) n
        (componentPushCycles f e n d (a d)) y) +
      (∑ᶠ d, CycleGroup.toAlgebraicCycle
        ((dimensionComponent Y e).hom.relativeDimensionFunction (fun _ ↦ 0)) n
        (componentPushCycles f e n d (b d)) y)
    have hterm (d : ℕ) : CycleGroup.toAlgebraicCycle
        ((dimensionComponent Y e).hom.relativeDimensionFunction (fun _ ↦ 0)) n
        (componentPushCycles f e n d ((a + b) d)) y =
      CycleGroup.toAlgebraicCycle
        ((dimensionComponent Y e).hom.relativeDimensionFunction (fun _ ↦ 0)) n
        (componentPushCycles f e n d (a d)) y +
      CycleGroup.toAlgebraicCycle
        ((dimensionComponent Y e).hom.relativeDimensionFunction (fun _ ↦ 0)) n
        (componentPushCycles f e n d (b d)) y := by
      rw [Pi.add_apply, (componentPushCycles f e n d).map_add]
      rfl
    simp_rw [hterm]
    exact finsum_add_distrib
      ((properComponentImages_locallyFinite f e n a).point_finite y)
      ((properComponentImages_locallyFinite f e n b).point_finite y)
  unfold mapDegreeCycleClass
  rw [hadd, map_add]

private def dimensionCycleQuotient (X : SchemeOverField k) [Smooth X.hom] (n : ℤ) :
    (∀ d, CycleGroup (dimensionComponent X d).left
      ((dimensionComponent X d).hom.relativeDimensionFunction (fun _ ↦ 0)) n) →+
    (∀ d, RelativeChow (fun _ ↦ 0) (dimensionComponent X d) n) where
  toFun a d := @chowClass (dimensionComponent X d).left
    (LocallyOfFiniteType.isLocallyNoetherian (dimensionComponent X d).hom)
    ((dimensionComponent X d).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n (a d)
  map_zero' := by ext d; exact map_zero _
  map_add' a b := by ext d; exact map_add _ _ _

/-- Homogeneous completed proper pushforward, descended from locally finite cycle sums. -/
@[no_expose] def mapDegree (f : X ⟶ Y) [IsProper f.left] (e : ℕ) (n : ℤ) :
    (∀ d, RelativeChow (fun _ ↦ 0) (dimensionComponent X d) n) →+
    RelativeChow (fun _ ↦ 0) (dimensionComponent Y e) n :=
  (dimensionCycleQuotient X n).liftOfSurjective
    (by
      intro a
      exact ⟨fun d ↦ Quotient.out (a d), funext fun d ↦ Quotient.out_eq (a d)⟩)
    ⟨{ toFun := mapDegreeCycleClass f e n
       map_zero' := mapDegree_zero f e n
       map_add' := mapDegree_add f e n }, by
      intro a ha
      apply (@chowClass_eq_zero_iff (dimensionComponent Y e).left
        (LocallyOfFiniteType.isLocallyNoetherian (dimensionComponent Y e).hom)
        ((dimensionComponent Y e).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n _).mpr
      apply mapDegree_mem_boundaries f e n a
      intro d
      apply (@chowClass_eq_zero_iff (dimensionComponent X d).left
        (LocallyOfFiniteType.isLocallyNoetherian (dimensionComponent X d).hom)
        ((dimensionComponent X d).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n _).mp
      exact congrFun ha d⟩

/-- Evaluation in a homogeneous degree on all dimension components. -/
def degreeComponents (X : SchemeOverField k) [Smooth X.hom] (n : ℤ) :
    DimensionCompleted X →+
      (∀ d, RelativeChow (fun _ ↦ 0) (dimensionComponent X d) n) where
  toFun a d := a d n
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Proper pushforward on dimension-completed Chow homology, assembled in each target component
from its homogeneous degrees `0,…,e`. -/
def map (f : X ⟶ Y) [IsProper f.left] : DimensionCompleted X →+ DimensionCompleted Y :=
  AddMonoidHom.pi fun e ↦ ∑ n ∈ Finset.range (e + 1),
    ((DirectSum.of (fun n : ℤ ↦ RelativeChow (fun _ ↦ 0) (dimensionComponent Y e) n)
      (n : ℤ)).comp (mapDegree f e n)).comp (degreeComponents X n)

/-- Completed proper pushforward extends ordinary total Chow pushforward. -/
theorem map_embed (f : X ⟶ Y) [IsProper f.left] (a : Total (fun _ ↦ 0) X) :
    map f (embed X a) = embed Y (Total.map (fun _ ↦ 0) f a) := sorry

/-- The homogeneous Gysin cap from a target dimension component to its source inverse image. -/
def smoothGysinComponentDegree (f : X ⟶ Y) (d e : ℕ) (n : ℤ) :
    RelativeChow (fun _ ↦ 0) (dimensionComponent Y e) (n + ((e : ℤ) - d)) →+
    Clopen.homology (fun _ ↦ 0) (dimensionComponent X d)
      (sourceTargetDimensionLocus f d e) n :=
  (AddEquiv.cast (by omega :
    n + ((e : ℤ) - d) - ((e : ℤ) - d) = n)).toAddMonoidHom.comp
    ((@BivariantClass.smoothGysinClassOfDimensions k _
      (sourceTargetDimensionComponent f d e) (dimensionComponent Y e)
      (inferInstanceAs (Smooth
        ((sourceTargetDimensionLocus f d e).ι ≫ (dimensionComponent X d).hom)))
      inferInstance (sourceTargetDimensionMap f d e) d e
      (sourceTargetDimensionLocus_relativeDimension f d e) inferInstance).cap
      (𝟙 (sourceTargetDimensionComponent f d e)) (sourceTargetDimensionMap f d e)
      (𝟙 (dimensionComponent Y e)) IsPullback.of_id_fst (n + ((e : ℤ) - d)))

/-- The homogeneous completed Gysin map, glued along the inverse images of target dimensions. -/
@[no_expose] def smoothGysinDegree (f : X ⟶ Y) (d : ℕ) (n : ℤ) :
    DimensionCompleted Y →+ RelativeChow (fun _ ↦ 0) (dimensionComponent X d) n :=
  (Clopen.assemble (fun _ ↦ 0) (dimensionComponent X d) (sourceTargetDimensionLocus f d)
    (sourceTarget_closed f d) (sourceTarget_disjoint f d) (sourceTarget_cover f d) n).comp
    (show DimensionCompleted Y →+
      (∀ e, Clopen.homology (fun _ ↦ 0) (dimensionComponent X d)
        (sourceTargetDimensionLocus f d e) n) from
      { toFun := fun b e ↦ smoothGysinComponentDegree f d e n
          (degreeEvaluation (dimensionComponent Y e) (n + ((e : ℤ) - d)) (b e))
        map_zero' := by
          funext e
          exact (smoothGysinComponentDegree f d e n).map_zero
        map_add' a b := by
          funext e
          exact (smoothGysinComponentDegree f d e n).map_add _ _ })

/-- Canonical Gysin pullback between arbitrary smooth schemes on dimension-completed integral
Chow homology. -/
def smoothGysinMap (f : X ⟶ Y) : DimensionCompleted Y →+ DimensionCompleted X :=
  AddMonoidHom.pi fun d ↦ ∑ n ∈ Finset.range (d + 1),
    (DirectSum.of (fun n : ℤ ↦ RelativeChow (fun _ ↦ 0) (dimensionComponent X d) n)
      (n : ℤ)).comp (smoothGysinDegree f d n)

/-- Restriction of a completed Gysin class to a source-target dimension locus is its canonical
constant-dimensional Gysin cap in every degree. -/
theorem smoothGysinMap_component (f : X ⟶ Y) (b : DimensionCompleted Y)
    (d e : ℕ) (n : ℤ) :
    Clopen.restrict (fun _ ↦ 0) (dimensionComponent X d) (sourceTargetDimensionLocus f d e) n
      (smoothGysinMap f b d n) =
      smoothGysinComponentDegree f d e n (b e (n + ((e : ℤ) - d))) := sorry

/-- The completed smooth product extends the total smooth product on quasi-compact schemes. -/
theorem embed_smoothIntersectionProduct (X : SchemeOverField k) [Smooth X.hom]
    [CompactSpace X.left] (a b : Total (fun _ ↦ 0) X) :
    embed X (Total.smoothIntersectionProduct X a b) =
      smoothIntersectionProduct X (embed X a) (embed X b) := sorry

/-- The canonical completed intersection product agrees with every rank-locus diagonal model. -/
theorem smoothIntersectionProduct_eq_ofRankLoci (X : SchemeOverField k) [Smooth X.hom]
    (D : ∀ d, DiagonalSpecializationOfRankLoci (dimensionComponent X d)) :
    smoothIntersectionProduct X = intersectionProduct X D := sorry

/-- On total input, canonical completed Gysin pullback agrees with the graph construction
on all source dimension components. -/
theorem smoothGysinMap_embed_eq_ofRankLoci (f : X ⟶ Y)
    (D : ∀ d, GraphSpecializationOfRankLoci (dimensionComponentι X d ≫ f))
    (b : Total (fun _ ↦ 0) Y) :
    smoothGysinMap f (embed Y b) = ChowGroup.gysinMapOfRankLoci f D b := sorry

end AlgebraicGeometry.ChowGroup.DimensionCompleted
