module

public import stacks_project.Chap62.Lemma_62_11_1_Cap
public import stacks_project.Chap62.Lemma_62_5_1_Operations

/-!
# Composition of families of cycles on fibres

This file constructs the composite family of cycles on fibres of `X ⟶ S` from a
family on fibres of `X ⟶ Y` and a family on fibres of `Y ⟶ S`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The morphism of scheme-theoretic fibres `X_s ⟶ Y_s` induced by `f : X ⟶ Y`
over `S`. -/
noncomputable abbrev compFiberMap {X Y S : Scheme.{u}} (f : X ⟶ Y) (p : Y ⟶ S)
    (s : S) : (f ≫ p).fiber s ⟶ p.fiber s :=
  idTriangleFiberMap f rfl s

/-- The comparison morphism `X_s ⟶ Y_s` is locally of finite type when `X ⟶ Y`
is. -/
instance instLocallyOfFiniteType_compFiberMap {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (p : Y ⟶ S) [LocallyOfFiniteType f] (s : S) :
    LocallyOfFiniteType (compFiberMap f p s) := sorry

/-- The square relating the composite fibre `X_s` to the fibre `Y_s` along
`f : X ⟶ Y` is cartesian. -/
theorem isPullback_fiberι_idTriangleFiberMap {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (p : Y ⟶ S) (s : S) :
    IsPullback ((f ≫ p).fiberι s) (compFiberMap f p s) f (p.fiberι s) := sorry

namespace CyclesOnFibers

/-- Base change of a family of `r`-cycles on fibres of `X / Y` along
`Y_s ⟶ Y`, as a family of `r`-cycles on fibres of `X_s / Y_s`. -/
noncomputable def baseChangeFiberι {X Y S : Scheme.{u}} {f : X ⟶ Y}
    (p : Y ⟶ S) [LocallyOfFiniteType f] {r : ℤ} (α : CyclesOnFibers f r)
    (s : S) : CyclesOnFibers (compFiberMap f p s) r :=
  FiberCycleFamily.baseChange (isPullback_fiberι_idTriangleFiberMap f p s) α

/-- The fibrewise cap used to form the composite family is supported in
relative dimension `r + e` on the fibre of `X / S`. -/
theorem comp_mem_dimensionSubgroup {X Y S : Scheme.{u}} {f : X ⟶ Y}
    {p : Y ⟶ S} [LocallyOfFiniteType f] [LocallyOfFiniteType p] {r e : ℤ}
    (α : CyclesOnFibers f r) (β : CyclesOnFibers p e) (s : S) :
    CycleGroup.toAlgebraicCycle
        ((compFiberMap f p s ≫ p.fiberToSpecResidueField s).relativeDimensionFunction
          (fun _ ↦ 0)) (r + e)
        (cap (p.fiberToSpecResidueField s) (compFiberMap f p s) (fun _ ↦ 0)
          (baseChangeFiberι p α s) (β s)) ∈
      AlgebraicCycle.dimensionSubgroup ((f ≫ p).fiberCycleDimension s) (r + e) :=
    sorry

/-- Composition of a family of `r`-cycles on fibres of `X / Y` with a family of
`e`-cycles on fibres of `Y / S`. At a point `s` of `S`, this is the fibrewise
cap of the base change of `α` along `Y_s ⟶ Y` with `β s`. -/
noncomputable def comp {X Y S : Scheme.{u}} {f : X ⟶ Y} {p : Y ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType p] {r e : ℤ}
    (α : CyclesOnFibers f r) (β : CyclesOnFibers p e) :
    CyclesOnFibers (f ≫ p) (r + e) :=
  fun s ↦
    ⟨CycleGroup.toAlgebraicCycle
        ((compFiberMap f p s ≫ p.fiberToSpecResidueField s).relativeDimensionFunction
          (fun _ ↦ 0)) (r + e)
        (cap (p.fiberToSpecResidueField s) (compFiberMap f p s) (fun _ ↦ 0)
          (baseChangeFiberι p α s) (β s)),
      comp_mem_dimensionSubgroup α β s⟩

/-- Evaluating the composite family at `s` recovers the fibrewise formula
`(Y_s ⟶ Y)*α ∩ β_s`. -/
theorem comp_apply {X Y S : Scheme.{u}} {f : X ⟶ Y} {p : Y ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType p] {r e : ℤ}
    (α : CyclesOnFibers f r) (β : CyclesOnFibers p e) (s : S) :
    CycleGroup.toAlgebraicCycle ((f ≫ p).fiberCycleDimension s) (r + e)
        (comp α β s) =
      CycleGroup.toAlgebraicCycle
        ((compFiberMap f p s ≫ p.fiberToSpecResidueField s).relativeDimensionFunction
          (fun _ ↦ 0)) (r + e)
        (cap (p.fiberToSpecResidueField s) (compFiberMap f p s) (fun _ ↦ 0)
          (baseChangeFiberι p α s) (β s)) := sorry

/-- Composition with the zero family of cycles on fibres of `X / Y` is zero. -/
theorem comp_zero_left {X Y S : Scheme.{u}} {f : X ⟶ Y} {p : Y ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType p] {r e : ℤ}
    (β : CyclesOnFibers p e) :
    comp (0 : CyclesOnFibers f r) β = 0 := sorry

/-- Composition with the zero family of cycles on fibres of `Y / S` is zero. -/
theorem comp_zero_right {X Y S : Scheme.{u}} {f : X ⟶ Y} {p : Y ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType p] {r e : ℤ}
    (α : CyclesOnFibers f r) :
    comp α (0 : CyclesOnFibers p e) = 0 := sorry

end CyclesOnFibers

end AlgebraicGeometry.Scheme.Hom
