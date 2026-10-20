/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RationalFunction

/-!
# Rational functions at generic points

This file gives the comparison maps from the rational-function ring of a scheme with finitely
many irreducible components to the stalks and residue fields at its component generic points.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The comparison from the rational-function ring of a scheme with finitely many irreducible
components to the product of the stalks at its component generic points. -/
def rationalFunctionRingToPiStalk (X : Scheme.{u})
    [Finite (irreducibleComponents X)] :
    X.rationalFunctionRing →+* ∀ η : genericPoints X, X.presheaf.stalk η.1 := by
  classical
  let point_mem : ∀ (U : RationalFunction.DenseOpenIndex X) (η : genericPoints X),
      (η.1 : X) ∈ U.1 := by
    intro U η
    let Z : irreducibleComponents X := genericPoints.component η
    let V : Set X := (⋃₀ (irreducibleComponents X \ {(Z : Set X)}))ᶜ
    have hV_open : IsOpen V := by
      dsimp [V]
      rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
      exact (Set.toFinite (irreducibleComponents X)).sdiff.isClosed_biUnion
        fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
    have hV_closure : closure V = (Z : Set X) :=
      closure_sUnion_irreducibleComponents_sdiff_singleton
        (Set.toFinite (irreducibleComponents X)) Z.1 Z.2
    have hV_nonempty : V.Nonempty := by
      apply Set.Nonempty.of_closure
      rw [hV_closure]
      exact Z.2.1.nonempty
    obtain ⟨x, hxV, hxU⟩ := U.2.inter_open_nonempty V hV_open hV_nonempty
    apply (genericPoints.isGenericPoint η).mem_open_set_iff U.1.isOpen |>.2
    exact ⟨x, hV_closure ▸ subset_closure hxV, hxU⟩
  refine Ring.DirectLimit.lift
    (fun U : RationalFunction.DenseOpenIndex X ↦ RationalFunction.sections X U)
    (fun U V hUV ↦
      (RationalFunction.restriction X U V hUV :
        RationalFunction.sections X U → RationalFunction.sections X V))
    (∀ η : genericPoints X, X.presheaf.stalk η.1)
    (fun U ↦ RingHom.pi fun η ↦
      (X.presheaf.germ U.1 η.1 (point_mem U η)).hom) ?_
  intro U V hUV s
  ext η
  exact X.presheaf.germ_res_apply (homOfLE hUV) η.1 (point_mem V η) s

/-- A section representing a rational function maps to its germ at every component generic
point. -/
@[simp]
theorem rationalFunctionRingToPiStalk_stage_apply (X : Scheme.{u})
    [Finite (irreducibleComponents X)] (U : RationalFunction.DenseOpenIndex X)
    (s : RationalFunction.sections X U) (η : genericPoints X) (hη : (η.1 : X) ∈ U.1) :
    X.rationalFunctionRingToPiStalk (RationalFunction.stage X U s) η =
      X.presheaf.germ U.1 η.1 hη s := by
  simp [rationalFunctionRingToPiStalk, RationalFunction.stage]

/-- For a scheme with finitely many irreducible components, the comparison from its
rational-function ring to the product of the component-generic stalks is bijective. -/
theorem rationalFunctionRingToPiStalk_bijective (X : Scheme.{u})
    [Finite (irreducibleComponents X)] :
    Function.Bijective
      (X.rationalFunctionRingToPiStalk :
        X.rationalFunctionRing → ∀ η : genericPoints X, X.presheaf.stalk η.1) := sorry

/-- The comparison from the rational-function ring to the product of the residue fields at
component generic points. -/
def rationalFunctionRingToPiResidueField (X : Scheme.{u})
    [Finite (irreducibleComponents X)] :
    X.rationalFunctionRing →+* ∀ η : genericPoints X, X.residueField η.1 :=
  RingHom.pi fun η ↦
    (X.residue η.1).hom.comp
      ((Pi.evalRingHom (fun η : genericPoints X ↦ X.presheaf.stalk η.1) η).comp
        X.rationalFunctionRingToPiStalk)

/-- The residue-field comparison is obtained by applying the residue map to each
component-generic stalk value. -/
@[simp]
theorem rationalFunctionRingToPiResidueField_apply (X : Scheme.{u})
    [Finite (irreducibleComponents X)] (f : X.rationalFunctionRing)
    (η : genericPoints X) :
    X.rationalFunctionRingToPiResidueField f η =
      X.residue η.1 (X.rationalFunctionRingToPiStalk f η) := rfl

/-- For a reduced scheme with finitely many irreducible components, the comparison from its
rational-function ring to the product of the component-generic residue fields is bijective. -/
theorem rationalFunctionRingToPiResidueField_bijective (X : Scheme.{u})
    [Finite (irreducibleComponents X)] [IsReduced X] :
    Function.Bijective
      (X.rationalFunctionRingToPiResidueField :
        X.rationalFunctionRing → ∀ η : genericPoints X, X.residueField η.1) := sorry

/-- The comparison from the rational-function ring of an integral scheme to the residue field
at its generic point. -/
def rationalFunctionRingToResidueField_genericPoint (X : Scheme.{u}) [IsIntegral X] :
    X.rationalFunctionRing →+* X.residueField (genericPoint X) :=
  (X.residue (genericPoint X)).hom.comp
    X.rationalFunctionRing_equiv_functionField.toRingHom

/-- The generic-point residue-field comparison is the residue map applied after the canonical
rational-function/function-field equivalence. -/
@[simp]
theorem rationalFunctionRingToResidueField_genericPoint_apply (X : Scheme.{u}) [IsIntegral X]
    (f : X.rationalFunctionRing) :
    X.rationalFunctionRingToResidueField_genericPoint f =
      X.residue (genericPoint X) (X.rationalFunctionRing_equiv_functionField f) := rfl

/-- For an integral scheme, the comparison from its rational-function ring to the residue field
at the generic point is bijective. -/
theorem rationalFunctionRingToResidueField_genericPoint_bijective (X : Scheme.{u})
    [IsIntegral X] :
    Function.Bijective
      (X.rationalFunctionRingToResidueField_genericPoint :
        X.rationalFunctionRing → X.residueField (genericPoint X)) := sorry

end AlgebraicGeometry.Scheme
