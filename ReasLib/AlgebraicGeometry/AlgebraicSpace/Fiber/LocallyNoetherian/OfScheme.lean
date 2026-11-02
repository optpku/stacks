/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.LocallyNoetherian

/-!
# Locally Noetherian fibres of represented scheme morphisms

The comparison uses the scheme-theoretic fibre over the canonical residue-field
point. Local Noetherianity of its representing scheme is the same condition as
local Noetherianity of the corresponding field-valued fibre of algebraic spaces.
No finite-type or finite-presentation hypothesis is required.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Local Noetherianity of a represented scheme agrees with local Noetherianity
of its associated algebraic space. -/
theorem isLocallyNoetherian_ofOver_iff {S : Scheme.{u}} (T : Over S) :
    IsLocallyNoetherian (ofOver T) ↔ AlgebraicGeometry.IsLocallyNoetherian T.left :=
  sorry

/-- The field-valued fibre of a represented morphism over a canonical residue
point has the same local Noetherianity as the represented scheme-theoretic
fibre. Both sides use the pullback against `V.left.fromSpecResidueField v`.
This is a property comparison, with no choice of a representing scheme or an
inverse to an admitted isomorphism. -/
theorem isLocallyNoetherian_fieldFiber_ofScheme_residuePoint_iff
    {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V) (v : V.left) :
    IsLocallyNoetherian
        (fieldFiber (ofOverMap h)
          (FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint v))) ↔
      IsLocallyNoetherian (ofOver (Over.mk (h.left.fiberι v ≫ U.hom))) :=
  sorry

/-- For a represented morphism, locally Noetherian fibres mean exactly that
every scheme-theoretic residue-field fibre is locally Noetherian. -/
theorem locallyNoetherianFibers_ofOverMap_iff {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) :
    LocallyNoetherianFibers (ofOverMap h) ↔
      ∀ v : V.left, AlgebraicGeometry.IsLocallyNoetherian (h.left.fiber v) := by
  constructor
  · intro hN v
    haveI : Mono
        (FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint v)).hom := by
      let j : Over.mk (V.left.fromSpecResidueField v ≫ V.hom) ⟶ V :=
        Over.homMk (V.left.fromSpecResidueField v) rfl
      haveI : Mono j.left := by
        change Mono (V.left.fromSpecResidueField v)
        infer_instance
      haveI : Mono j := Over.mono_of_mono_left j
      haveI : Mono (yoneda.map j) := by
        constructor
        intro Z a b hab
        ext T point
        exact (cancel_mono j).mp (congrFun (congrArg (fun k ↦ k.app T) hab) point)
      constructor
      intro Z a b hab
      exact (cancel_mono (yoneda.map j)).mp hab
    have hF := (locallyNoetherianFiber_iff_of_mono (ofOverMap h)
      (ofOver.pointsEquiv V v)
      (FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint v))
      (ofOver.pointsEquiv_apply V v).symm).mpr (hN.fiber _).existsField
    exact (isLocallyNoetherian_ofOver_iff _).mp
      ((isLocallyNoetherian_fieldFiber_ofScheme_residuePoint_iff h v).mp hF)
  · intro hN
    constructor
    intro y
    obtain ⟨v, rfl⟩ := (ofOver.pointsEquiv V).surjective y
    constructor
    refine ⟨FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint v),
      (ofOver.pointsEquiv_apply V v).symm, ?_⟩
    exact (isLocallyNoetherian_fieldFiber_ofScheme_residuePoint_iff h v).mpr
      ((isLocallyNoetherian_ofOver_iff _).mpr (hN v))

/-- A scheme morphism with locally Noetherian fibres retains this property
when viewed as a morphism of algebraic spaces. -/
instance instLocallyNoetherianFibers_ofOverMap {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V)
    [hN : ∀ v : V.left, AlgebraicGeometry.IsLocallyNoetherian (h.left.fiber v)] :
    LocallyNoetherianFibers (ofOverMap h) :=
  (locallyNoetherianFibers_ofOverMap_iff h).mpr hN

end AlgebraicGeometry.AlgebraicSpace
