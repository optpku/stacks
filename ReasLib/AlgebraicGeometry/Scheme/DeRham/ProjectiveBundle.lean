/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.CanonicalAction
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.Realization
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.LerayHirsch.Absolute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open RingedSite.Hom AlgebraicGeometry.Scheme.DeRham.DerivedPushforward
open scoped MonoidalCategory TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.ProjectiveBundle

variable {S X P : Scheme.{u}}

/-- A projective-bundle projection and its composite with the base morphism form a
commutative square over the base scheme. -/
theorem structureSquare (f : X ⟶ S) (π : P ⟶ X) :
    CommSq π (π ≫ f) f (𝟙 S) := sorry

/-- The logarithmic first Chern class of the tautological invertible module. -/
def tautologicalLogarithmicClass {E : X.Modules} (f : X ⟶ S) (π : P ⟶ X)
    (hπ : Scheme.ProjectiveBundle.Representation π E) :
    LogarithmicForms.H (π ≫ f) 1 1 :=
  LogarithmicForms.firstChernHom (π ≫ f)
    (@Scheme.Modules.picardClass P (Scheme.ProjectiveBundle.tautologicalSheaf π hπ)
      (Scheme.ProjectiveBundle.tautologicalSheaf_isInvertible π hπ))

/-- The cup powers of a supplied de Rham realization of the tautological logarithmic class. -/
def chernPower {E : X.Modules} (f : X ⟶ S) (π : P ⟶ X)
    (hπ : Scheme.ProjectiveBundle.Representation π E)
    (D : LogarithmicForms.ChernComparison (π ≫ f)) :
    (degree : ℕ) → cohomology (π ≫ f) (2 * (degree : ℤ)) :=
  CanonicalAction.evenPower (π ≫ f)
    (LogarithmicForms.toDeRhamCohomology (π ≫ f) D (tautologicalLogarithmicClass f π hπ))

/-- Each successor supplied Chern power is its preceding power cupped with the
supplied de Rham realization of the tautological logarithmic class. -/
theorem chernPower_def {E : X.Modules} (f : X ⟶ S) (π : P ⟶ X)
    (hπ : Scheme.ProjectiveBundle.Representation π E)
    (D : LogarithmicForms.ChernComparison (π ≫ f)) (degree : ℕ) :
    chernPower f π hπ D (degree + 1) =
      (eqToHom (congrArg (cohomology (π ≫ f)) (CanonicalAction.twiceSuccDegree degree))).hom
        ((CanonicalAction.cupMorphism (π ≫ f) (2 * (degree : ℤ)) 2).hom
          (chernPower f π hπ D degree ⊗ₜ
            LogarithmicForms.toDeRhamCohomology (π ≫ f) D
              (tautologicalLogarithmicClass f π hπ))) := rfl

/-- The canonical cup powers of the de Rham first Chern class of the tautological module. -/
def canonicalChernPower {E : X.Modules} (f : X ⟶ S) (π : P ⟶ X)
    (hπ : Scheme.ProjectiveBundle.Representation π E) :
    (degree : ℕ) → cohomology (π ≫ f) (2 * (degree : ℤ)) :=
  CanonicalAction.evenPower (π ≫ f)
    (LogarithmicForms.canonicalToDeRhamCohomology (π ≫ f)
      (tautologicalLogarithmicClass f π hπ))

/-- The canonical degree-two action of the tautological de Rham first Chern class. -/
def canonicalFirstChernMap {E : X.Modules} (f : X ⟶ S) (π : P ⟶ X)
    (hπ : Scheme.ProjectiveBundle.Representation π E) :
    ShiftedHom (derivedComplex (π ≫ f)) (derivedComplex (π ≫ f)) (2 : ℤ) :=
  CanonicalAction.map (π ≫ f) 2
    (LogarithmicForms.canonicalToDeRhamCohomology (π ≫ f)
      (tautologicalLogarithmicClass f π hπ))

-- Local instance justification (defeq pin): the formula uses the named canonical coefficient pushforward model, not a caller-supplied derived-functor choice.
attribute [local instance] CanonicalTensor.coefficientPushforward_hasRightDerived

/-- The direct-sum map given by pullback and left cup multiplication by canonical
tautological Chern powers in each cohomological degree. -/
def cohomologyMap (f : X ⟶ S) (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (π : P ⟶ X)
    (hπ : Scheme.ProjectiveBundle.Representation π E) (q : ℤ) :=
  LerayHirsch.overBaseCohomologyMap (structureSquare f π)
    (fun degree : Fin r ↦ 2 * (degree : ℕ))
    (fun degree ↦ canonicalChernPower f π hπ degree) q

/-- The projective-bundle cohomology map sends each direct-sum generator to its
pullback cupped on the left with the corresponding canonical tautological Chern power. -/
theorem cohomologyMap_lof_apply (f : X ⟶ S) (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (π : P ⟶ X)
    (hπ : Scheme.ProjectiveBundle.Representation π E)
    (q : ℤ) (i : Fin r)
    (a : cohomology f (q - ((2 * (i : ℕ) : ℕ) : ℤ))) :
    (cohomologyMap f E r π hπ q).hom.comp
        (DirectSum.lof (coefficientRing f) (Fin r)
          (fun j ↦ cohomology f (q - ((2 * (j : ℕ) : ℕ) : ℤ))) i) a =
      (eqToHom (congrArg (Cohomology.restricted (structureSquare f π))
        ((add_comm ((2 * (i : ℕ) : ℕ) : ℤ)
          (q - ((2 * (i : ℕ) : ℕ) : ℤ))).trans
            (sub_add_cancel q ((2 * (i : ℕ) : ℕ) : ℤ))))).hom
        ((CanonicalAction.cupMorphism (π ≫ f) ((2 * (i : ℕ) : ℕ) : ℤ)
          (q - ((2 * (i : ℕ) : ℕ) : ℤ))).hom
            (canonicalChernPower f π hπ i ⊗ₜ
              (Cohomology.restrictedPullback (structureSquare f π)
                (q - ((2 * (i : ℕ) : ℕ) : ℤ))).hom a)) := sorry

/-- For a constant-rank locally free module, canonical tautological Chern powers
give an isomorphism from the direct sum of shifted de Rham cohomology modules of the
base to the de Rham cohomology of its represented projective bundle. -/
theorem cohomologyMapIsIso (f : X ⟶ S) (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (π : P ⟶ X)
    (hπ : Scheme.ProjectiveBundle.Representation π E) (q : ℤ) :
    IsIso (cohomologyMap f E r π hπ q) := sorry

/-- The degree-two shifted endomorphism given by a supplied realization of the
tautological first Chern class. -/
def firstChernMap {E : X.Modules} (f : X ⟶ S) (π : P ⟶ X)
    (hπ : Scheme.ProjectiveBundle.Representation π E)
    (D : LogarithmicForms.ChernComparison (π ≫ f)) :
    ShiftedHom (derivedComplex (π ≫ f)) (derivedComplex (π ≫ f)) (2 : ℤ) :=
  CanonicalAction.map (π ≫ f) 2
    (LogarithmicForms.toDeRhamCohomology (π ≫ f) D (tautologicalLogarithmicClass f π hπ))

/-- The supplied tautological first-Chern action is the class action of its supplied
de Rham realization. -/
theorem firstChernMap_def {E : X.Modules} (f : X ⟶ S) (π : P ⟶ X)
    (hπ : Scheme.ProjectiveBundle.Representation π E)
    (D : LogarithmicForms.ChernComparison (π ≫ f)) :
    firstChernMap f π hπ D = CanonicalAction.map (π ≫ f) 2
      (LogarithmicForms.toDeRhamCohomology (π ≫ f) D
        (tautologicalLogarithmicClass f π hπ)) := sorry

/-- The recursively accumulated integer degree of an iterated first-Chern action. -/
def chernMapDegree : ℕ → ℤ := CanonicalAction.evenDegree

/-- The degree of `degree` iterated first-Chern actions is `2 * degree`. -/
theorem chernMapDegree_eq (degree : ℕ) : chernMapDegree degree = 2 * (degree : ℤ) :=
  CanonicalAction.evenDegree_eq degree

/-- The recursive shifted iteration of a supplied tautological first-Chern action. -/
def chernMapPower {E : X.Modules} (f : X ⟶ S) (π : P ⟶ X)
    (hπ : Scheme.ProjectiveBundle.Representation π E)
    (D : LogarithmicForms.ChernComparison (π ≫ f)) :
    (degree : ℕ) → ShiftedHom (derivedComplex (π ≫ f))
      (derivedComplex (π ≫ f)) (chernMapDegree degree) :=
  CanonicalAction.iterateDegreeTwo (firstChernMap f π hπ D)

/-- The recursive shifted iteration of the canonical tautological first-Chern action. -/
def canonicalChernMapPower {E : X.Modules} (f : X ⟶ S) (π : P ⟶ X)
    (hπ : Scheme.ProjectiveBundle.Representation π E) :
    (degree : ℕ) → ShiftedHom (derivedComplex (π ≫ f))
      (derivedComplex (π ≫ f)) (chernMapDegree degree) :=
  CanonicalAction.iterateDegreeTwo (canonicalFirstChernMap f π hπ)

/-- The zeroth iterated first-Chern action is the shifted identity in degree zero. -/
theorem chernMapPower_zero {E : X.Modules} (f : X ⟶ S) (π : P ⟶ X)
    (hπ : Scheme.ProjectiveBundle.Representation π E)
    (D : LogarithmicForms.ChernComparison (π ≫ f)) :
    chernMapPower f π hπ D 0 = ShiftedHom.mk₀ 0 rfl (𝟙 _) := sorry

/-- Each successor first-Chern action is obtained by composition with the degree-two action. -/
theorem chernMapPower_succ {E : X.Modules} (f : X ⟶ S) (π : P ⟶ X)
    (hπ : Scheme.ProjectiveBundle.Representation π E)
    (D : LogarithmicForms.ChernComparison (π ≫ f)) (degree : ℕ) :
    chernMapPower f π hπ D (degree + 1) =
      (chernMapPower f π hπ D degree).comp (firstChernMap f π hπ D) rfl := sorry

/-- After degree normalization, the canonical iterated action is multiplication by the
canonical tautological Chern power. -/
theorem canonicalChernMapPower_eq_classAction {E : X.Modules} (f : X ⟶ S) (π : P ⟶ X)
    (hπ : Scheme.ProjectiveBundle.Representation π E) (t : ℕ) :
    cast (congrArg (fun n : ℤ ↦ ShiftedHom (derivedComplex (π ≫ f))
      (derivedComplex (π ≫ f)) n) (chernMapDegree_eq t))
        (canonicalChernMapPower f π hπ t) =
      CanonicalAction.map (π ≫ f) (2 * (t : ℤ)) (canonicalChernPower f π hπ t) := sorry

-- Local instance justification (defeq pin): pushed first-Chern actions use the specified total-derived coefficient pushforward shift.
attribute [local instance] CanonicalTensor.pushforwardCommShift

/-- The supplied degree-two tautological first-Chern action after derived pushforward. -/
def pushedFirstChernMap {E : X.Modules} (f : X ⟶ S) (π : P ⟶ X)
    (hπ : Scheme.ProjectiveBundle.Representation π E)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (Cohomology.coefficientHom (structureSquare f π)))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite (π ≫ f).toLRSHom.toShHom))]
    (D : LogarithmicForms.ChernComparison (π ≫ f)) :
    ShiftedHom
      ((modulePushforwardDerived.{u} (Cohomology.coefficientHom (structureSquare f π))).obj
        (derivedComplex (π ≫ f)))
      ((modulePushforwardDerived.{u} (Cohomology.coefficientHom (structureSquare f π))).obj
        (derivedComplex (π ≫ f))) (2 : ℤ) :=
  (modulePushforwardDerived.{u} (Cohomology.coefficientHom (structureSquare f π))).shiftedHomMap
    (Iso.refl _) (Iso.refl _) 2 (firstChernMap f π hπ D)

/-- The canonical degree-two tautological first-Chern action after derived pushforward. -/
def canonicalPushedFirstChernMap {E : X.Modules} (f : X ⟶ S) (π : P ⟶ X)
    (hπ : Scheme.ProjectiveBundle.Representation π E)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived (Cohomology.coefficientHom (structureSquare f π)))
      (ModuleQis (RingedSpace.DeRham.coefficientSite (π ≫ f).toLRSHom.toShHom))] :
    ShiftedHom
      ((modulePushforwardDerived (Cohomology.coefficientHom (structureSquare f π))).obj
        (derivedComplex (π ≫ f)))
      ((modulePushforwardDerived (Cohomology.coefficientHom (structureSquare f π))).obj
        (derivedComplex (π ≫ f))) (2 : ℤ) :=
  (modulePushforwardDerived (Cohomology.coefficientHom (structureSquare f π))).shiftedHomMap
    (Iso.refl _) (Iso.refl _) 2 (canonicalFirstChernMap f π hπ)

/-- The pushed first-Chern action is the shift-compatible image of the first-Chern action. -/
theorem pushedFirstChernMap_def {E : X.Modules} (f : X ⟶ S) (π : P ⟶ X)
    (hπ : Scheme.ProjectiveBundle.Representation π E)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (Cohomology.coefficientHom (structureSquare f π)))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite (π ≫ f).toLRSHom.toShHom))]
    (D : LogarithmicForms.ChernComparison (π ≫ f)) :
    pushedFirstChernMap f π hπ D =
      (modulePushforwardDerived.{u} (Cohomology.coefficientHom (structureSquare f π))).shiftedHomMap
        (Iso.refl _) (Iso.refl _) 2 (firstChernMap f π hπ D) := sorry

end AlgebraicGeometry.Scheme.DeRham.ProjectiveBundle
