/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup.FlatBaseChange
public import ReasLib.AlgebraicGeometry.CycleGroup.Reindex
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.DiscreteValuation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction.FlatCompatibility
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange

/-!
# Base change and specialization of cycles

The generic- and special-fibre cycle maps along an extension of discrete
valuation rings are residue-field flat pullbacks followed by fibre comparison.
Specialization commutes with these two base-change maps.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.AffineBaseChange

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup

/-- Field-extension base change of `r`-cycles from the generic fibre `X_K` to
the generic fibre `X'_{K'}` of `X' = X_{R'}`. -/
noncomputable def genericFiberBaseChange (R R' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] (r : ℕ) :
    CycleGroup f.genericFiber
        (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r →+
      CycleGroup (toBase R R' f).genericFiber
        ((toBase R R' f).fiberDimensionFunction
          (genericPoint (Spec (CommRingCat.of R')))) r :=
  let g := specMap R R'
  let s' := genericPoint (Spec (CommRingCat.of R'))
  let dPull :=
    (pullback.snd (f.fiberToSpecResidueField (g s'))
        (Spec.map (g.residueFieldMap s'))).relativeDimensionFunction
      (fun _ ↦ 0)
  (mapHom
        (isPullback_baseChangeFiberMap f g (toSource R R' f) (toBase R R' f)
            (IsPullback.of_hasPullback f g) s').isoPullback.symm.hom
        dPull ((toBase R R' f).fiberDimensionFunction s') r).comp
    ((reindex dPull (add_zero (r : ℤ))).comp
      ((baseChangePullback (Spec.map (g.residueFieldMap s'))
          (fun _ ↦ 0) (fun _ ↦ 0) 0
          (isDimensionFunctionCompatible_zero (Spec.map (g.residueFieldMap s')))
          (f.fiberToSpecResidueField (g s')) r).comp
        (mapHom (genericFiberPointHom R R' f)
          (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R))))
          (f.fiberDimensionFunction (g s')) r)))

/-- Field-extension base change of `r`-cycles from the special fibre `X_κ` to
the special fibre `X'_{κ'}` of `X' = X_{R'}`. -/
noncomputable def specialFiberBaseChange (R R' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] (r : ℕ) :
    CycleGroup f.specialFiber
        (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r →+
      CycleGroup (toBase R R' f).specialFiber
        ((toBase R R' f).fiberDimensionFunction (IsLocalRing.closedPoint R')) r :=
  let g := specMap R R'
  let s' := IsLocalRing.closedPoint R'
  let dPull :=
    (pullback.snd (f.fiberToSpecResidueField (g s'))
        (Spec.map (g.residueFieldMap s'))).relativeDimensionFunction
      (fun _ ↦ 0)
  (mapHom
        (isPullback_baseChangeFiberMap f g (toSource R R' f) (toBase R R' f)
            (IsPullback.of_hasPullback f g) s').isoPullback.symm.hom
        dPull ((toBase R R' f).fiberDimensionFunction s') r).comp
    ((reindex dPull (add_zero (r : ℤ))).comp
      ((baseChangePullback (Spec.map (g.residueFieldMap s'))
          (fun _ ↦ 0) (fun _ ↦ 0) 0
          (isDimensionFunctionCompatible_zero (Spec.map (g.residueFieldMap s')))
          (f.fiberToSpecResidueField (g s')) r).comp
        (mapHom (specialFiberPointHom R R' f)
          (f.fiberDimensionFunction (IsLocalRing.closedPoint R))
          (f.fiberDimensionFunction (g s')) r)))

/-- Unfolding `genericFiberBaseChange` as residue-field pullback, reindexing
`r + 0 = r`, and transport along the fibre identification. -/
theorem genericFiberBaseChange_eq (R R' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] (r : ℕ) :
    genericFiberBaseChange R R' f r =
      let g := specMap R R'
      let s' := genericPoint (Spec (CommRingCat.of R'))
      let dPull :=
        (pullback.snd (f.fiberToSpecResidueField (g s'))
            (Spec.map (g.residueFieldMap s'))).relativeDimensionFunction
          (fun _ ↦ 0)
      (mapHom
            (isPullback_baseChangeFiberMap f g (toSource R R' f) (toBase R R' f)
                (IsPullback.of_hasPullback f g) s').isoPullback.symm.hom
            dPull ((toBase R R' f).fiberDimensionFunction s') r).comp
        ((reindex dPull (add_zero (r : ℤ))).comp
          ((baseChangePullback (Spec.map (g.residueFieldMap s'))
              (fun _ ↦ 0) (fun _ ↦ 0) 0
              (isDimensionFunctionCompatible_zero (Spec.map (g.residueFieldMap s')))
              (f.fiberToSpecResidueField (g s')) r).comp
            (mapHom (genericFiberPointHom R R' f)
              (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R))))
              (f.fiberDimensionFunction (g s')) r))) := sorry

/-- Unfolding `specialFiberBaseChange` as residue-field pullback, reindexing
`r + 0 = r`, and transport along the fibre identification. -/
theorem specialFiberBaseChange_eq (R R' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] (r : ℕ) :
    specialFiberBaseChange R R' f r =
      let g := specMap R R'
      let s' := IsLocalRing.closedPoint R'
      let dPull :=
        (pullback.snd (f.fiberToSpecResidueField (g s'))
            (Spec.map (g.residueFieldMap s'))).relativeDimensionFunction
          (fun _ ↦ 0)
      (mapHom
            (isPullback_baseChangeFiberMap f g (toSource R R' f) (toBase R R' f)
                (IsPullback.of_hasPullback f g) s').isoPullback.symm.hom
            dPull ((toBase R R' f).fiberDimensionFunction s') r).comp
        ((reindex dPull (add_zero (r : ℤ))).comp
          ((baseChangePullback (Spec.map (g.residueFieldMap s'))
              (fun _ ↦ 0) (fun _ ↦ 0) 0
              (isDimensionFunctionCompatible_zero (Spec.map (g.residueFieldMap s')))
              (f.fiberToSpecResidueField (g s')) r).comp
            (mapHom (specialFiberPointHom R R' f)
              (f.fiberDimensionFunction (IsLocalRing.closedPoint R))
              (f.fiberDimensionFunction (g s')) r))) := sorry

/-- Evaluating generic-fibre field-extension base change on an `r`-cycle. -/
theorem genericFiberBaseChange_apply (R R' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] (r : ℕ)
    (α : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r) :
    genericFiberBaseChange R R' f r α =
      let g := specMap R R'
      let s' := genericPoint (Spec (CommRingCat.of R'))
      let dPull :=
        (pullback.snd (f.fiberToSpecResidueField (g s'))
            (Spec.map (g.residueFieldMap s'))).relativeDimensionFunction
          (fun _ ↦ 0)
      mapHom
          (isPullback_baseChangeFiberMap f g (toSource R R' f) (toBase R R' f)
              (IsPullback.of_hasPullback f g) s').isoPullback.symm.hom
          dPull ((toBase R R' f).fiberDimensionFunction s') r
        (reindex dPull (add_zero (r : ℤ))
          (baseChangePullback (Spec.map (g.residueFieldMap s'))
            (fun _ ↦ 0) (fun _ ↦ 0) 0
            (isDimensionFunctionCompatible_zero (Spec.map (g.residueFieldMap s')))
            (f.fiberToSpecResidueField (g s')) r
            (mapHom (genericFiberPointHom R R' f)
              (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R))))
              (f.fiberDimensionFunction (g s')) r α))) := sorry

/-- Evaluating special-fibre field-extension base change on an `r`-cycle. -/
theorem specialFiberBaseChange_apply (R R' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] (r : ℕ)
    (α : CycleGroup f.specialFiber
      (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r) :
    specialFiberBaseChange R R' f r α =
      let g := specMap R R'
      let s' := IsLocalRing.closedPoint R'
      let dPull :=
        (pullback.snd (f.fiberToSpecResidueField (g s'))
            (Spec.map (g.residueFieldMap s'))).relativeDimensionFunction
          (fun _ ↦ 0)
      mapHom
          (isPullback_baseChangeFiberMap f g (toSource R R' f) (toBase R R' f)
              (IsPullback.of_hasPullback f g) s').isoPullback.symm.hom
          dPull ((toBase R R' f).fiberDimensionFunction s') r
        (reindex dPull (add_zero (r : ℤ))
          (baseChangePullback (Spec.map (g.residueFieldMap s'))
            (fun _ ↦ 0) (fun _ ↦ 0) 0
            (isDimensionFunctionCompatible_zero (Spec.map (g.residueFieldMap s')))
            (f.fiberToSpecResidueField (g s')) r
            (mapHom (specialFiberPointHom R R' f)
              (f.fiberDimensionFunction (IsLocalRing.closedPoint R))
              (f.fiberDimensionFunction (g s')) r α))) := sorry

/-- Specialization of cycles commutes with generic- and special-fibre base change
along an extension of discrete valuation rings. -/
@[stacks 0H4K]
theorem cycleSpecialization_comp_baseChange
    {R R' : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (r : ℕ) :
    ((toBase R R' f).cycleSpecialization r).comp (genericFiberBaseChange R R' f r) =
      (specialFiberBaseChange R R' f r).comp (f.cycleSpecialization r) := sorry

/-- Specialization of an `r`-cycle on the generic fibre of `X / R`, then base
change to the special fibre of `X' / R'`, agrees with base change on the
generic fibre followed by specialization over `R'`. -/
theorem cycleSpecialization_baseChange
    {R R' : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (r : ℕ)
    (α : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r) :
    (toBase R R' f).cycleSpecialization r (genericFiberBaseChange R R' f r α) =
      specialFiberBaseChange R R' f r (f.cycleSpecialization r α) := sorry

end AlgebraicGeometry.CycleGroup
