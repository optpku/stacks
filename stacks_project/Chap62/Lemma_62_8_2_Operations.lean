module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import stacks_project.Chap62.Lemma_62_6_6_Family

/-!
# Restriction, flat pullback, and proper pushforward of fibre cycle families

This file constructs the three missing family-level operations on
`RelativeCycle.Family`: restriction to a morphism of opens over `f`, flat
pullback of relative dimension `e`, and proper pushforward over the base.
Base change is already defined in `Lemma_62_6_6_Family`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Function Set

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

variable {X S : Scheme.{u}}

/-- The comparison morphism from a restricted fibre of `φ : U ⟶ V` to the
original fibre of `f` over `V.ι t`. -/
noncomputable def restrictFiberMap (f : X ⟶ S) (U : X.Opens) (V : S.Opens)
    (φ : U.toScheme ⟶ V.toScheme) (hφ : φ ≫ V.ι = U.ι ≫ f) (t : V.toScheme) :
    φ.fiber t ⟶ f.fiber (V.ι t) :=
  Scheme.Hom.fiberMap φ U.ι V.ι f ⟨hφ.symm⟩ t

/-- Restricting fibre-cycle coefficients along `restrictFiberMap` has locally
finite support. -/
theorem restrict_locallyFiniteSupport (f : X ⟶ S) {r : ℕ} (α : Family f r)
    (U : X.Opens) (V : S.Opens) (φ : U.toScheme ⟶ V.toScheme)
    (hφ : φ ≫ V.ι = U.ι ≫ f) (t : V.toScheme) :
    LocallyFiniteSupport fun x : φ.fiber t ↦
      CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction (V.ι t)) r (α (V.ι t))
        (restrictFiberMap f U V φ hφ t x) := sorry

/-- The algebraic cycle on a restricted fibre obtained by restricting
coefficients along `restrictFiberMap`. -/
noncomputable def restrictCycle (f : X ⟶ S) {r : ℕ} (α : Family f r)
    (U : X.Opens) (V : S.Opens) (φ : U.toScheme ⟶ V.toScheme)
    (hφ : φ ≫ V.ι = U.ι ≫ f) (t : V.toScheme) :
    AlgebraicCycle (φ.fiber t) ℤ where
  toFun := fun x ↦
    CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction (V.ι t)) r (α (V.ι t))
      (restrictFiberMap f U V φ hφ t x)
  supportWithinDomain' := subset_univ _
  supportLocallyFiniteWithinDomain' := fun x _ ↦
    restrict_locallyFiniteSupport f α U V φ hφ t x

/-- The restricted fibre cycle remains supported in dimension `r`. -/
theorem restrictCycle_mem_dimensionSubgroup (f : X ⟶ S) {r : ℕ} (α : Family f r)
    (U : X.Opens) (V : S.Opens) (φ : U.toScheme ⟶ V.toScheme)
    (hφ : φ ≫ V.ι = U.ι ≫ f) (t : V.toScheme) :
    restrictCycle f α U V φ hφ t ∈
      AlgebraicCycle.dimensionSubgroup (φ.fiberDimensionFunction t) r := sorry

/-- Restriction of a family of fibrewise `r`-cycles to a morphism of opens
`φ : U ⟶ V` over `f`. This is the source operation `α|_U`. -/
noncomputable def restrict {f : X ⟶ S} {r : ℕ} (U : X.Opens) (V : S.Opens)
    (φ : U.toScheme ⟶ V.toScheme) (hφ : φ ≫ V.ι = U.ι ≫ f) (α : Family f r) :
    Family φ r :=
  fun t ↦ ⟨restrictCycle f α U V φ hφ t,
    restrictCycle_mem_dimensionSubgroup f α U V φ hφ t⟩

/-- Coefficients of a restriction are the original fibre coefficients along
`restrictFiberMap`. -/
theorem restrict_apply {f : X ⟶ S} {r : ℕ} (U : X.Opens) (V : S.Opens)
    (φ : U.toScheme ⟶ V.toScheme) (hφ : φ ≫ V.ι = U.ι ≫ f) (α : Family f r)
    (t : V.toScheme) (x : φ.fiber t) :
    CycleGroup.toAlgebraicCycle (φ.fiberDimensionFunction t) r
        (restrict U V φ hφ α t) x =
      CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction (V.ι t)) r (α (V.ι t))
        (restrictFiberMap f U V φ hφ t x) := sorry

/-- The comparison morphism from a fibre of `p ≫ f` to the corresponding fibre
of `f`. -/
noncomputable def flatPullbackFiberMap {X' : Scheme.{u}} (f : X ⟶ S) (p : X' ⟶ X)
    (s : S) : (p ≫ f).fiber s ⟶ f.fiber s :=
  Scheme.Hom.fiberMap (p ≫ f) p (𝟙 S) f ⟨(Category.comp_id (p ≫ f)).symm⟩ s

/-- Fibrewise flat-pullback coefficients have locally finite support. -/
theorem flatPullback_locallyFiniteSupport {X' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (p : X' ⟶ X) [LocallyOfFiniteType p] (e : ℕ)
    {r : ℕ} (α : Family f r) (s : S) :
    LocallyFiniteSupport fun x' : (p ≫ f).fiber s ↦
      ∑ᶠ y : f.fiber s,
        CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s) y *
          CycleGroup.toAlgebraicCycle ((p ≫ f).fiberDimensionFunction s) (r + e)
            (Scheme.IdealSheafData.associatedCycle
              ((Scheme.PointClosure.reducedStructure y).ideal.comap
                (flatPullbackFiberMap f p s))
              ((p ≫ f).fiberDimensionFunction s) (r + e)) x' := sorry

/-- The algebraic cycle on a fibre of `p ≫ f` given by flat pullback of point
closures. -/
noncomputable def flatPullbackCycle {X' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (p : X' ⟶ X) [LocallyOfFiniteType p] (e : ℕ)
    {r : ℕ} (α : Family f r) (s : S) :
    AlgebraicCycle ((p ≫ f).fiber s) ℤ where
  toFun := fun x' ↦
    ∑ᶠ y : f.fiber s,
      CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s) y *
        CycleGroup.toAlgebraicCycle ((p ≫ f).fiberDimensionFunction s) (r + e)
          (Scheme.IdealSheafData.associatedCycle
            ((Scheme.PointClosure.reducedStructure y).ideal.comap
              (flatPullbackFiberMap f p s))
            ((p ≫ f).fiberDimensionFunction s) (r + e)) x'
  supportWithinDomain' := subset_univ _
  supportLocallyFiniteWithinDomain' := fun x' _ ↦
    flatPullback_locallyFiniteSupport f p e α s x'

/-- The flat-pulled-back fibre cycle is supported in dimension `r + e`. -/
theorem flatPullbackCycle_mem_dimensionSubgroup {X' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (p : X' ⟶ X) [LocallyOfFiniteType p] (e : ℕ)
    {r : ℕ} (α : Family f r) (s : S) :
    flatPullbackCycle f p e α s ∈
      AlgebraicCycle.dimensionSubgroup ((p ≫ f).fiberDimensionFunction s)
        (r + e) := sorry

/-- Flat pullback of a family of fibrewise `r`-cycles along a flat morphism of
relative dimension `e`. This is the source operation `p^*α`. -/
noncomputable def flatPullback {X' : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {r : ℕ} (p : X' ⟶ X) [Flat p]
    (e : ℕ) [Scheme.Hom.RelativeDimension p e] (α : Family f r) :
    Family (p ≫ f) (r + e) :=
  fun s ↦ ⟨flatPullbackCycle f p e α s,
    flatPullbackCycle_mem_dimensionSubgroup f p e α s⟩

/-- Coefficients of a flat pullback are the associated-cycle formula on the
compared fibre. -/
theorem flatPullback_apply {X' : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {r : ℕ} (p : X' ⟶ X) [Flat p]
    (e : ℕ) [Scheme.Hom.RelativeDimension p e] (α : Family f r)
    (s : S) (x' : (p ≫ f).fiber s) :
    CycleGroup.toAlgebraicCycle ((p ≫ f).fiberDimensionFunction s) (r + e)
        (flatPullback p e α s) x' =
      ∑ᶠ y : f.fiber s,
        CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s) y *
          CycleGroup.toAlgebraicCycle ((p ≫ f).fiberDimensionFunction s) (r + e)
            (Scheme.IdealSheafData.associatedCycle
              ((Scheme.PointClosure.reducedStructure y).ideal.comap
                (flatPullbackFiberMap f p s))
              ((p ≫ f).fiberDimensionFunction s) (r + e)) x' := sorry

/-- The comparison morphism from a fibre of `f` to the corresponding fibre of
`pY`, induced by a morphism `h : X ⟶ Y` over `S`. -/
noncomputable def pushforwardFiberMap {Y : Scheme.{u}} (f : X ⟶ S)
    (pY : Y ⟶ S) (h : X ⟶ Y) (hc : h ≫ pY = f) (s : S) :
    f.fiber s ⟶ pY.fiber s :=
  Scheme.Hom.fiberMap f h (𝟙 S) pY ⟨hc.trans (Category.comp_id f).symm⟩ s

/-- The fibre morphism of a proper morphism over a common base is proper. -/
instance instIsProper_pushforwardFiberMap {Y : Scheme.{u}} (f : X ⟶ S)
    (pY : Y ⟶ S) (h : X ⟶ Y) [IsProper h] (hc : h ≫ pY = f) (s : S) :
    IsProper (pushforwardFiberMap f pY h hc s) := sorry

/-- Proper pushforward of a family of fibrewise `r`-cycles along `h : X ⟶ Y`
over `S`. This is the source operation `h_*α`. -/
noncomputable def pushforward {Y : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {r : ℕ} (pY : Y ⟶ S) [LocallyOfFiniteType pY]
    (h : X ⟶ Y) [IsProper h] (hc : h ≫ pY = f) (α : Family f r) :
    Family pY r :=
  fun s ↦
    CycleGroup.mapHom (pushforwardFiberMap f pY h hc s)
      (f.fiberDimensionFunction s) (pY.fiberDimensionFunction s) r (α s)

/-- Coefficients of a proper pushforward are computed by `AlgebraicCycle.map`
along `pushforwardFiberMap`. -/
theorem pushforward_apply {Y : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {r : ℕ} (pY : Y ⟶ S) [LocallyOfFiniteType pY]
    (h : X ⟶ Y) [IsProper h] (hc : h ≫ pY = f) (α : Family f r) (s : S)
    (y : pY.fiber s) :
    CycleGroup.toAlgebraicCycle (pY.fiberDimensionFunction s) r
        (pushforward pY h hc α s) y =
      AlgebraicCycle.map (pushforwardFiberMap f pY h hc s)
        (f.fiberDimensionFunction s) (pY.fiberDimensionFunction s)
        (CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s)) y :=
  sorry

end AlgebraicGeometry.RelativeCycle
