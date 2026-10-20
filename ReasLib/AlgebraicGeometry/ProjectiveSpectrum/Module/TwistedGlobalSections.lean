/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.GlobalSections
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Sections

/-!
# Twisted global sections on a projective spectrum

The global sections of all integral twists of a module sheaf form an integer-graded module.
This file packages its canonical homogeneous action, associated sheaf, counit, and degreewise
maps as explicit data.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry

namespace ProjTwistedGlobalSections

variable {A : Type u} [CommRing A]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]

/-- The degree-`n` piece of the twisted-global-sections module of `F`. -/
abbrev degree (F : (Proj 𝒜).Modules) (n : ℤ) : Type u :=
  Γ(tensorObj F (Proj.AssociatedModule.twistingSheaf 𝒜 n), ⊤)

/-- The external direct sum of the global sections of all integral twists of `F`. -/
abbrev carrier (F : (Proj 𝒜).Modules) : Type u :=
  ⨁ n : ℤ, degree 𝒜 F n

/-- The canonical internal degree-`n` submodule of the twisted-global-sections direct sum. -/
abbrev grading (F : (Proj 𝒜).Modules) (n : ℤ) :
    Submodule ℤ (carrier 𝒜 F) :=
  LinearMap.range (DirectSum.lof ℤ ℤ (degree 𝒜 F) n)

end ProjTwistedGlobalSections

/-- Explicit canonical twisted-global-sections data for a module sheaf on a projective
spectrum. The total module is the direct sum of the global sections of all integral twists. -/
structure ProjTwistedGlobalSections {A : Type u} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (F : (Proj 𝒜).Modules) where
  /-- The module action of the graded ring on the twisted-section direct sum. -/
  moduleAction : Module A (ProjTwistedGlobalSections.carrier 𝒜 F)
  /-- The module action respects the canonical direct-sum grading. -/
  gradedAction :
    -- Local instance justification (defeq pin): the stored explicit module action is supplied to the dependent graded-action type without registering it.
    letI : Module A (ProjTwistedGlobalSections.carrier 𝒜 F) := moduleAction
    SetLike.GradedSMul 𝒜 (ProjTwistedGlobalSections.grading 𝒜 F)
  /-- Multiplication of the canonical twisting sheaves. -/
  twistMultiplication : Proj.AssociatedModule.TwistMultiplication 𝒜
  /-- Comparison of the associated module sheaf after tensoring with a canonical twist. -/
  shiftComparison :
    -- Local instance justification (defeq pin): the stored explicit module action is supplied to the dependent shift-comparison type without registering it.
    letI : Module A (ProjTwistedGlobalSections.carrier 𝒜 F) := moduleAction
    -- Local instance justification (defeq pin): the stored explicit graded action is supplied to the dependent shift-comparison type without registering it.
    letI : SetLike.GradedSMul 𝒜 (ProjTwistedGlobalSections.grading 𝒜 F) :=
      gradedAction
    Proj.AssociatedModule.ShiftComparison 𝒜
      (ProjTwistedGlobalSections.grading 𝒜 F)
  /-- The canonical morphism from the sheaf associated to twisted global sections to `F`. -/
  counit :
    -- Local instance justification (defeq pin): the stored explicit module action is supplied to the dependent counit type without registering it.
    letI : Module A (ProjTwistedGlobalSections.carrier 𝒜 F) := moduleAction
    -- Local instance justification (defeq pin): the stored explicit graded action is supplied to the dependent counit type without registering it.
    letI : SetLike.GradedSMul 𝒜 (ProjTwistedGlobalSections.grading 𝒜 F) :=
      gradedAction
    Proj.AssociatedModule.sheaf 𝒜
        (ProjTwistedGlobalSections.grading 𝒜 F) ⟶ F
  /-- The endomorphism of the degree-`n` twisted global sections induced by the counit. -/
  degreeMap : ∀ n : ℤ,
    ProjTwistedGlobalSections.degree 𝒜 F n →+
      ProjTwistedGlobalSections.degree 𝒜 F n
  /-- On homogeneous elements, the stored module action is the action obtained from canonical
  twist sections and multiplication of twisting sheaves. -/
  homogeneousAction_formula :
    -- Local instance justification (defeq pin): the stored explicit module action is supplied to the homogeneous-action law without registering it.
    letI : Module A (ProjTwistedGlobalSections.carrier 𝒜 F) := moduleAction
    ∀ {d : ℕ} (a : 𝒜 d) (n : ℤ)
      (x : ProjTwistedGlobalSections.degree 𝒜 F n),
      (a : A) • DirectSum.of (ProjTwistedGlobalSections.degree 𝒜 F) n x =
        DirectSum.of (ProjTwistedGlobalSections.degree 𝒜 F) ((d : ℤ) + n)
          (ProjTwistGlobalSections.homogeneousAction 𝒜
            (Proj.AssociatedModule.twistingSheaf 𝒜) twistMultiplication.hom F d n
              (Proj.AssociatedModule.twistSection 𝒜 a) x)
  /-- On a positive-degree projective standard open, the counit sends the section represented
  by a homogeneous fraction `x / f` to the canonical local contraction: after tensoring with
  the restricted twist section of `f`, it is the restriction of `x`. The shift comparison sends
  the same tensor to the degree-zero section represented by `x` in the translated grading. -/
  counit_standardOpen_formula :
    -- Local instance justification (defeq pin): the stored explicit module action is supplied to the standard-open counit law without registering it.
    letI : Module A (ProjTwistedGlobalSections.carrier 𝒜 F) := moduleAction
    -- Local instance justification (defeq pin): the stored explicit graded action is supplied to the standard-open counit law without registering it.
    letI : SetLike.GradedSMul 𝒜 (ProjTwistedGlobalSections.grading 𝒜 F) :=
      gradedAction
    ∀ {d : ℕ} (f : 𝒜 d) (hd : 0 < d)
      (x : ProjTwistedGlobalSections.degree 𝒜 F (d : ℤ))
      (z : Proj.AssociatedModule.away 𝒜
        (ProjTwistedGlobalSections.grading 𝒜 F) f)
      (_ : (z : LocalizedModule.Away (f : A)
          (ProjTwistedGlobalSections.carrier 𝒜 F)) =
        HomogeneousLocalization.Away.Module.powMk 𝒜 f 1
          (DirectSum.of (ProjTwistedGlobalSections.degree 𝒜 F) (d : ℤ) x))
      (m : GradedModule.shiftGrading
        (ProjTwistedGlobalSections.grading 𝒜 F) (d : ℤ) 0)
      (_ : (m : ProjTwistedGlobalSections.carrier 𝒜 F) =
        DirectSum.of (ProjTwistedGlobalSections.degree 𝒜 F) (d : ℤ) x),
      let U := Proj.basicOpen 𝒜 (f : A)
      let tensorFraction :=
        SheafOfModules.RingedSite.tensorSection (Proj 𝒜).sheaf (op U)
          (Proj.AssociatedModule.awaySection 𝒜
            (ProjTwistedGlobalSections.grading 𝒜 F) f hd z)
          (((Proj.AssociatedModule.twistingSheaf 𝒜 (d : ℤ)).val.map
            (homOfLE (le_top : U ≤ (⊤ : (Proj 𝒜).Opens))).op).hom
              (Proj.AssociatedModule.twistSection 𝒜 f))
      (((shiftComparison.hom (d : ℤ)).val.app (op U)).hom tensorFraction =
          Proj.AssociatedModule.restrict 𝒜
            (GradedModule.shiftGrading
              (ProjTwistedGlobalSections.grading 𝒜 F) (d : ℤ)) le_top
            (Proj.AssociatedModule.degreeZeroToGlobalSections 𝒜
              (GradedModule.shiftGrading
                (ProjTwistedGlobalSections.grading 𝒜 F) (d : ℤ)) m)) ∧
        ((((counit ⊗ₘ 𝟙 (Proj.AssociatedModule.twistingSheaf 𝒜 (d : ℤ))).val.app
              (op U)).hom tensorFraction) =
          (((tensorObj F (Proj.AssociatedModule.twistingSheaf 𝒜 (d : ℤ)) :
              (Proj 𝒜).Modules).val.map
            (homOfLE (le_top : U ≤ (⊤ : (Proj 𝒜).Opens))).op).hom x))
  /-- On every degree-one standard open, the induced degree map restricts to the identity. -/
  degreeMap_standardOpen_formula :
    ∀ (f : 𝒜 1) (n : ℤ) (x : ProjTwistedGlobalSections.degree 𝒜 F n),
      (((tensorObj F (Proj.AssociatedModule.twistingSheaf 𝒜 n) :
          (Proj 𝒜).Modules).val.map
            (homOfLE (le_top :
              Proj.basicOpen 𝒜 (f : A) ≤ (⊤ : (Proj 𝒜).Opens))).op).hom
          (degreeMap n x)) =
        (((tensorObj F (Proj.AssociatedModule.twistingSheaf 𝒜 n) :
          (Proj 𝒜).Modules).val.map
            (homOfLE (le_top :
              Proj.basicOpen 𝒜 (f : A) ≤ (⊤ : (Proj 𝒜).Opens))).op).hom x)

namespace ProjTwistedGlobalSections

variable {A : Type u} [CommRing A]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
variable (F : (Proj 𝒜).Modules)

/-- Construct twisted-global-sections data from the concrete canonical action, comparisons,
counit, and degree maps with their homogeneous, standard-open contraction, and restriction
formulas. -/
def ofCanonicalAction
    (moduleAction : Module A (carrier 𝒜 F))
    (gradedAction :
      -- Local instance justification (defeq pin): the explicit module action is supplied to the dependent graded-action argument without registering it.
      letI : Module A (carrier 𝒜 F) := moduleAction
      SetLike.GradedSMul 𝒜 (grading 𝒜 F))
    (twistMultiplication : Proj.AssociatedModule.TwistMultiplication 𝒜)
    (shiftComparison :
      -- Local instance justification (defeq pin): the explicit module action is supplied to the dependent shift-comparison argument without registering it.
      letI : Module A (carrier 𝒜 F) := moduleAction
      -- Local instance justification (defeq pin): the explicit graded action is supplied to the dependent shift-comparison argument without registering it.
      letI : SetLike.GradedSMul 𝒜 (grading 𝒜 F) := gradedAction
      Proj.AssociatedModule.ShiftComparison 𝒜 (grading 𝒜 F))
    (counit :
      -- Local instance justification (defeq pin): the explicit module action is supplied to the dependent counit argument without registering it.
      letI : Module A (carrier 𝒜 F) := moduleAction
      -- Local instance justification (defeq pin): the explicit graded action is supplied to the dependent counit argument without registering it.
      letI : SetLike.GradedSMul 𝒜 (grading 𝒜 F) := gradedAction
      Proj.AssociatedModule.sheaf 𝒜 (grading 𝒜 F) ⟶ F)
    (degreeMap : ∀ n : ℤ, degree 𝒜 F n →+ degree 𝒜 F n)
    (homogeneousAction_formula :
      -- Local instance justification (defeq pin): the explicit module action is supplied to the homogeneous-action argument without registering it.
      letI : Module A (carrier 𝒜 F) := moduleAction
      ∀ {d : ℕ} (a : 𝒜 d) (n : ℤ) (x : degree 𝒜 F n),
        (a : A) • DirectSum.of (degree 𝒜 F) n x =
          DirectSum.of (degree 𝒜 F) ((d : ℤ) + n)
            (ProjTwistGlobalSections.homogeneousAction 𝒜
              (Proj.AssociatedModule.twistingSheaf 𝒜) twistMultiplication.hom F d n
                (Proj.AssociatedModule.twistSection 𝒜 a) x))
    (counit_standardOpen_formula :
      -- Local instance justification (defeq pin): the explicit module action is supplied to the standard-open counit argument without registering it.
      letI : Module A (carrier 𝒜 F) := moduleAction
      -- Local instance justification (defeq pin): the explicit graded action is supplied to the standard-open counit argument without registering it.
      letI : SetLike.GradedSMul 𝒜 (grading 𝒜 F) := gradedAction
      ∀ {d : ℕ} (f : 𝒜 d) (hd : 0 < d) (x : degree 𝒜 F (d : ℤ))
        (z : Proj.AssociatedModule.away 𝒜 (grading 𝒜 F) f)
        (_ : (z : LocalizedModule.Away (f : A) (carrier 𝒜 F)) =
          HomogeneousLocalization.Away.Module.powMk 𝒜 f 1
            (DirectSum.of (degree 𝒜 F) (d : ℤ) x))
        (m : GradedModule.shiftGrading (grading 𝒜 F) (d : ℤ) 0)
        (_ : (m : carrier 𝒜 F) =
          DirectSum.of (degree 𝒜 F) (d : ℤ) x),
        let U := Proj.basicOpen 𝒜 (f : A)
        let tensorFraction :=
          SheafOfModules.RingedSite.tensorSection (Proj 𝒜).sheaf (op U)
            (Proj.AssociatedModule.awaySection 𝒜 (grading 𝒜 F) f hd z)
            (((Proj.AssociatedModule.twistingSheaf 𝒜 (d : ℤ)).val.map
              (homOfLE (le_top : U ≤ (⊤ : (Proj 𝒜).Opens))).op).hom
                (Proj.AssociatedModule.twistSection 𝒜 f))
        (((shiftComparison.hom (d : ℤ)).val.app (op U)).hom tensorFraction =
            Proj.AssociatedModule.restrict 𝒜
              (GradedModule.shiftGrading (grading 𝒜 F) (d : ℤ)) le_top
              (Proj.AssociatedModule.degreeZeroToGlobalSections 𝒜
                (GradedModule.shiftGrading (grading 𝒜 F) (d : ℤ)) m)) ∧
          ((((counit ⊗ₘ 𝟙 (Proj.AssociatedModule.twistingSheaf 𝒜 (d : ℤ))).val.app
                (op U)).hom tensorFraction) =
            (((tensorObj F (Proj.AssociatedModule.twistingSheaf 𝒜 (d : ℤ)) :
                (Proj 𝒜).Modules).val.map
              (homOfLE (le_top : U ≤ (⊤ : (Proj 𝒜).Opens))).op).hom x)))
    (degreeMap_standardOpen_formula :
      ∀ (f : 𝒜 1) (n : ℤ) (x : degree 𝒜 F n),
        (((tensorObj F (Proj.AssociatedModule.twistingSheaf 𝒜 n) :
            (Proj 𝒜).Modules).val.map
              (homOfLE (le_top :
                Proj.basicOpen 𝒜 (f : A) ≤ (⊤ : (Proj 𝒜).Opens))).op).hom
            (degreeMap n x)) =
          (((tensorObj F (Proj.AssociatedModule.twistingSheaf 𝒜 n) :
            (Proj 𝒜).Modules).val.map
              (homOfLE (le_top :
                Proj.basicOpen 𝒜 (f : A) ≤ (⊤ : (Proj 𝒜).Opens))).op).hom x)) :
    AlgebraicGeometry.ProjTwistedGlobalSections 𝒜 F where
  moduleAction := moduleAction
  gradedAction := gradedAction
  twistMultiplication := twistMultiplication
  shiftComparison := shiftComparison
  counit := counit
  degreeMap := degreeMap
  homogeneousAction_formula := homogeneousAction_formula
  counit_standardOpen_formula := counit_standardOpen_formula
  degreeMap_standardOpen_formula := degreeMap_standardOpen_formula

/-- The sheaf associated to the canonically graded module of twisted global sections. -/
noncomputable def associatedSheaf
    (C : AlgebraicGeometry.ProjTwistedGlobalSections 𝒜 F) : (Proj 𝒜).Modules :=
  -- Local instance justification (defeq pin): the stored module action is supplied to the associated-sheaf constructor without registering a global instance.
  letI : Module A (carrier 𝒜 F) := C.moduleAction
  -- Local instance justification (defeq pin): the stored graded action is supplied to the associated-sheaf constructor without registering a global instance.
  letI : SetLike.GradedSMul 𝒜 (grading 𝒜 F) := C.gradedAction
  Proj.AssociatedModule.sheaf 𝒜 (grading 𝒜 F)

/-- The defining conditions identify the stored action with homogeneous twist multiplication,
identify the counit on standard homogeneous fractions by restriction and contraction, and make
every degree map locally the identity on degree-one standard opens. -/
theorem spec (C : AlgebraicGeometry.ProjTwistedGlobalSections 𝒜 F) :
    (
      -- Local instance justification (defeq pin): the stored explicit module action is supplied to the homogeneous-action specification without registering it.
      letI : Module A (carrier 𝒜 F) := C.moduleAction
      ∀ {d : ℕ} (a : 𝒜 d) (n : ℤ) (x : degree 𝒜 F n),
        (a : A) • DirectSum.of (degree 𝒜 F) n x =
          DirectSum.of (degree 𝒜 F) ((d : ℤ) + n)
            (ProjTwistGlobalSections.homogeneousAction 𝒜
              (Proj.AssociatedModule.twistingSheaf 𝒜) C.twistMultiplication.hom F d n
                (Proj.AssociatedModule.twistSection 𝒜 a) x)) ∧
      (
       -- Local instance justification (defeq pin): the stored explicit module action is supplied to the standard-open counit specification without registering it.
       letI : Module A (carrier 𝒜 F) := C.moduleAction
       -- Local instance justification (defeq pin): the stored explicit graded action is supplied to the standard-open counit specification without registering it.
       letI : SetLike.GradedSMul 𝒜 (grading 𝒜 F) := C.gradedAction
       ∀ {d : ℕ} (f : 𝒜 d) (hd : 0 < d) (x : degree 𝒜 F (d : ℤ))
        (z : Proj.AssociatedModule.away 𝒜 (grading 𝒜 F) f)
        (_ : (z : LocalizedModule.Away (f : A) (carrier 𝒜 F)) =
          HomogeneousLocalization.Away.Module.powMk 𝒜 f 1
            (DirectSum.of (degree 𝒜 F) (d : ℤ) x))
        (m : GradedModule.shiftGrading (grading 𝒜 F) (d : ℤ) 0)
        (_ : (m : carrier 𝒜 F) =
          DirectSum.of (degree 𝒜 F) (d : ℤ) x),
        let U := Proj.basicOpen 𝒜 (f : A)
        let tensorFraction :=
          SheafOfModules.RingedSite.tensorSection (Proj 𝒜).sheaf (op U)
            (Proj.AssociatedModule.awaySection 𝒜 (grading 𝒜 F) f hd z)
            (((Proj.AssociatedModule.twistingSheaf 𝒜 (d : ℤ)).val.map
              (homOfLE (le_top : U ≤ (⊤ : (Proj 𝒜).Opens))).op).hom
                (Proj.AssociatedModule.twistSection 𝒜 f))
        (((C.shiftComparison.hom (d : ℤ)).val.app (op U)).hom tensorFraction =
            Proj.AssociatedModule.restrict 𝒜
              (GradedModule.shiftGrading (grading 𝒜 F) (d : ℤ)) le_top
              (Proj.AssociatedModule.degreeZeroToGlobalSections 𝒜
                (GradedModule.shiftGrading (grading 𝒜 F) (d : ℤ)) m)) ∧
          ((((C.counit ⊗ₘ
              𝟙 (Proj.AssociatedModule.twistingSheaf 𝒜 (d : ℤ))).val.app
                (op U)).hom tensorFraction) =
            (((tensorObj F (Proj.AssociatedModule.twistingSheaf 𝒜 (d : ℤ)) :
                (Proj 𝒜).Modules).val.map
              (homOfLE (le_top : U ≤ (⊤ : (Proj 𝒜).Opens))).op).hom x))) ∧
      (∀ (f : 𝒜 1) (n : ℤ) (x : degree 𝒜 F n),
        (((tensorObj F (Proj.AssociatedModule.twistingSheaf 𝒜 n) :
            (Proj 𝒜).Modules).val.map
              (homOfLE (le_top :
                Proj.basicOpen 𝒜 (f : A) ≤ (⊤ : (Proj 𝒜).Opens))).op).hom
            (C.degreeMap n x)) =
          (((tensorObj F (Proj.AssociatedModule.twistingSheaf 𝒜 n) :
            (Proj 𝒜).Modules).val.map
              (homOfLE (le_top :
                Proj.basicOpen 𝒜 (f : A) ≤ (⊤ : (Proj 𝒜).Opens))).op).hom x)) := sorry

end ProjTwistedGlobalSections

end AlgebraicGeometry
