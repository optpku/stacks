/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalBridge
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalTail
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.StableRelativeAmple

/-!
# Stable curves and the stable locus of a family

This file records the unbundled property of being a stable curve over a field, the two
standard geometric characterizations of that property, and the open locus in the base of a
prestable family consisting of points whose residue-field fibres are stable curves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.DerivedQCoh
open AlgebraicGeometry.SchemeOverField
open Scheme.DerivedQCoh.ProperDualizingComplex
open SheafOfModules
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A scheme over a field is a stable curve when it is proper, at-worst-nodal, of dimension
one, has constant global functions, has cohomology genus at least two, and has neither a
rational tail nor a rational bridge. -/
def isStableCurve {k : Type u} [Field k] (X : SchemeOverField k) : Prop :=
  IsProper X.hom ∧ atWorstNodal X ∧ topologicalKrullDim X.left = 1 ∧
    Function.Bijective (Scheme.Hom.globalSectionsMap X.hom) ∧
    2 ≤ Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 ∧
    ¬ Nonempty (RationalTail X) ∧ ¬ Nonempty (RationalBridge X)

/-- A proper scheme of dimension at most one over a field is a stable curve if and only if it
is at-worst-nodal of dimension one, has constant global functions, has genus at least two, and
has neither a rational tail nor a rational bridge. -/
theorem isStableCurve_iff {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    isStableCurve X ↔
      atWorstNodal X ∧
        ∃ (hdim1 : topologicalKrullDim X.left = 1)
          (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
          2 ≤ genus X hdim1 hΓ ∧
            ¬ Nonempty (RationalTail X) ∧ ¬ Nonempty (RationalBridge X) :=
  sorry

/-- A proper scheme of dimension at most one over a field is a stable curve if and only if it
is at-worst-nodal of dimension one, has constant global functions, and has ample canonical
dualizing module. -/
theorem isStableCurve_iff_curveDualizingModule_isAmple
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    isStableCurve X ↔
      atWorstNodal X ∧ topologicalKrullDim X.left = 1 ∧
        Function.Bijective (Scheme.Hom.globalSectionsMap X.hom) ∧
        Scheme.Modules.isAmpleObject (curveDualizingModule X.hom) :=
  sorry

end AlgebraicGeometry.SchemeOverField

namespace AlgebraicGeometry.Scheme.Hom

/-- The set of target points whose residue-field fibres are stable curves. -/
def stableLocus {X S : Scheme.{u}} (f : X ⟶ S) : Set S :=
  {s | isStableCurve (Over.mk (f.fiberToSpecResidueField s))}

/-- Membership in the stable locus is the stable-curve property of the residue-field fibre. -/
theorem mem_stableLocus {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    s ∈ f.stableLocus ↔ isStableCurve (Over.mk (f.fiberToSpecResidueField s)) :=
  Iff.rfl

/-- For a prestable family of curves, the locus of points with stable residue-field fibres is
open. -/
theorem stableLocus_isOpen {X S : Scheme.{u}} (f : X ⟶ S) [AtWorstNodal f] [IsProper f]
    [(pushforwardCohomologyIn f).IsLeftAdjoint]
    (h_unit : ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
      IsIso (commRingSheafPushforwardMap (pullback.snd f g).toShHom)) :
    IsOpen f.stableLocus :=
  sorry

/-- The canonical open of the base consisting of points whose residue-field fibres are stable
curves. -/
def stableOpen {X S : Scheme.{u}} (f : X ⟶ S) [AtWorstNodal f] [IsProper f]
    [(pushforwardCohomologyIn f).IsLeftAdjoint]
    (h_unit : ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
      IsIso (commRingSheafPushforwardMap (pullback.snd f g).toShHom)) :
    S.Opens :=
  ⟨f.stableLocus, f.stableLocus_isOpen h_unit⟩

/-- Membership in the stable open is the stable-curve property of the residue-field fibre. -/
theorem mem_stableOpen {X S : Scheme.{u}} (f : X ⟶ S) [AtWorstNodal f] [IsProper f]
    [(pushforwardCohomologyIn f).IsLeftAdjoint]
    (h_unit : ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
      IsIso (commRingSheafPushforwardMap (pullback.snd f g).toShHom))
    (s : S) :
    s ∈ f.stableOpen h_unit ↔ isStableCurve (Over.mk (f.fiberToSpecResidueField s)) :=
  Iff.rfl

/-- The stable open of a prestable family is the whole base if and only if every residue-field
fibre is a stable curve. -/
theorem stableOpen_eq_top_iff {X S : Scheme.{u}} (f : X ⟶ S) [AtWorstNodal f] [IsProper f]
    [(pushforwardCohomologyIn f).IsLeftAdjoint]
    (h_unit : ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
      IsIso (commRingSheafPushforwardMap (pullback.snd f g).toShHom)) :
    f.stableOpen h_unit = ⊤ ↔
      ∀ s : S, isStableCurve (Over.mk (f.fiberToSpecResidueField s)) :=
  sorry

/-- A morphism into the base of a prestable family factors through the stable open if and only
if every residue-field fibre of the pullback is a stable curve. -/
theorem factorsThrough_stableOpen_iff {X S T : Scheme.{u}} (f : X ⟶ S)
    [AtWorstNodal f] [IsProper f] [(pushforwardCohomologyIn f).IsLeftAdjoint]
    (h_unit : ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
      IsIso (commRingSheafPushforwardMap (pullback.snd f g).toShHom))
    (g : T ⟶ S) :
    (∃ lift : T ⟶ (f.stableOpen h_unit).toScheme,
      lift ≫ (f.stableOpen h_unit).ι = g) ↔
      ∀ t : T, isStableCurve (Over.mk ((pullback.snd f g).fiberToSpecResidueField t)) :=
  sorry

end AlgebraicGeometry.Scheme.Hom

