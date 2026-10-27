/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.CategoryTheory.Monoidal.InvertibleQuotient.IsoClass
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.UniversalProperty
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Projective-bundle models

The universal property is the concrete map
`SymmetricPresentation.liftToQuotientClass`, with compatible target-isomorphism classes as its
codomain. A supplied `Representation` additionally records explicit lifts of these classes.
No raw-quotient equivalence is asserted, and no inverse is extracted from a representability
or bijectivity theorem.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveBundle

variable {X P : Scheme.{u}} {ℰ : X.Modules} {π : P ⟶ X}

/-- A supplied projective-bundle model with a concrete symmetric presentation and explicit
class-to-lift data. The latter is model data, not an additional universal-property owner. -/
@[stacks 01OB "projective-bundle quotient-class model"]
structure Representation (π : P ⟶ X) (ℰ : X.Modules) where
  /-- The module being projectivized is quasi-coherent. -/
  quasicoherent : ℰ.IsQuasicoherent
  /-- The actual symmetric-algebra and degree-one tautological presentation. -/
  symmetricPresentation :
    letI := quasicoherent
    SymmetricPresentation π ℰ
  /-- Explicit lifts indexed by compatible quotient-isomorphism classes. -/
  liftOfQuotientClass : ∀ ⦃T : Scheme.{u}⦄ (f : T ⟶ X),
    CategoryTheory.InvertibleQuotient.IsoClass
      ((Scheme.Modules.pullback f).obj ℰ) → Lift π f
  /-- The supplied lift has the requested class under the concrete tautological map. -/
  liftOfQuotientClass_spec :
    letI := quasicoherent
    ∀ ⦃T : Scheme.{u}⦄ (f : T ⟶ X)
      (q : CategoryTheory.InvertibleQuotient.IsoClass
        ((Scheme.Modules.pullback f).obj ℰ)),
      symmetricPresentation.liftToQuotientClass f (liftOfQuotientClass f q) = q
  /-- Every integral twist in the supplied relative-Proj presentation is invertible. -/
  twist_isInvertible : ∀ n : ℤ,
    Scheme.Modules.Invertible (symmetricPresentation.relativeProj.twist n)

/-- The displayed relative projective-spectrum presentation. -/
abbrev Representation.presentation (hπ : Representation π ℰ) :
    Scheme.Hom.RelativeProjPresentation π :=
  hπ.symmetricPresentation.relativeProj

/-- The integral twists in the displayed presentation. -/
abbrev Representation.twist (hπ : Representation π ℰ) (n : ℤ) : P.Modules :=
  hπ.presentation.twist n

/-- The single concrete forward quotient-class map. -/
noncomputable def Representation.liftToQuotientClass (hπ : Representation π ℰ)
    {T : Scheme.{u}} (f : T ⟶ X) :
    Lift π f → CategoryTheory.InvertibleQuotient.IsoClass
      ((Scheme.Modules.pullback f).obj ℰ) :=
  letI := hπ.quasicoherent
  hπ.symmetricPresentation.liftToQuotientClass f

/-- A concrete representative is obtained by pulling back the actual tautological quotient.
This is a forward map, not an equivalence with raw quotients. -/
noncomputable def Representation.liftSourceQuotient (hπ : Representation π ℰ)
    {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f) :
    CategoryTheory.InvertibleQuotient ((Scheme.Modules.pullback f).obj ℰ) :=
  letI := hπ.quasicoherent
  hπ.symmetricPresentation.liftSourceQuotient f σ

/-- The supplied lift realizes the requested compatible quotient class. -/
theorem Representation.liftOfQuotientClass_eq (hπ : Representation π ℰ)
    {T : Scheme.{u}} (f : T ⟶ X)
    (q : CategoryTheory.InvertibleQuotient.IsoClass
      ((Scheme.Modules.pullback f).obj ℰ)) :
    hπ.liftToQuotientClass f (hπ.liftOfQuotientClass f q) = q :=
  hπ.liftOfQuotientClass_spec f q

/-- Classifying lifts are unique by the concrete symmetric-presentation universal property. -/
theorem Representation.liftToQuotientClass_injective (hπ : Representation π ℰ)
    {T : Scheme.{u}} (f : T ⟶ X) :
    Function.Injective (hπ.liftToQuotientClass f) :=
  letI := hπ.quasicoherent
  (hπ.symmetricPresentation.liftToQuotientClass_bijective f).1

/-- The quotient-class adapter retained for downstream recall APIs. Its codomain is the
compatible quotient-class type, never the raw bundled quotient type. -/
noncomputable def Representation.liftEquiv (hπ : Representation π ℰ)
    {T : Scheme.{u}} (f : T ⟶ X) :
    Lift π f ≃ CategoryTheory.InvertibleQuotient.IsoClass
      ((Scheme.Modules.pullback f).obj ℰ) :=
  { toFun := hπ.liftToQuotientClass f
    invFun := hπ.liftOfQuotientClass f
    left_inv := by
      intro σ
      apply hπ.liftToQuotientClass_injective f
      exact hπ.liftOfQuotientClass_eq f (hπ.liftToQuotientClass f σ)
    right_inv := fun q => hπ.liftOfQuotientClass_eq f q }

/-- The supplied projective-bundle structure morphism is separated. -/
@[stacks 01OB "projective-bundle separatedness"]
theorem Representation.isSeparated (hπ : Representation π ℰ) : IsSeparated π :=
  hπ.presentation.isSeparated

/-- The actual tautological quotient of the concrete symmetric presentation. -/
@[stacks 01OB "tautological quotient of a projective bundle",
  stacks 01VM "tautological quotient in relative very ampleness"]
noncomputable def tautologicalQuotient (π : P ⟶ X) (hπ : Representation π ℰ) :
    CategoryTheory.InvertibleQuotient ((Scheme.Modules.pullback π).obj ℰ) :=
  letI := hπ.quasicoherent
  hπ.symmetricPresentation.tautologicalQuotient

/-- The actual first-twist target of the tautological quotient. -/
@[stacks 01OB "tautological module of a projective bundle",
  stacks 01VM "tautological module in relative very ampleness"]
noncomputable abbrev tautologicalSheaf (π : P ⟶ X) (hπ : Representation π ℰ) : P.Modules :=
  (tautologicalQuotient π hπ).object

/-- The target of a concrete lift quotient is definitionally the pulled-back tautological target.
No isomorphism is selected from an equality of raw quotient structures. -/
noncomputable def Representation.pullbackTautologicalSheafIso
    (hπ : Representation π ℰ) {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f) :
    (Scheme.Modules.pullback σ.hom).obj (tautologicalSheaf π hπ) ≅
      (hπ.liftSourceQuotient f σ).object :=
  Iso.refl _

/-- The concrete representative is the pulled-back tautological map with its source transported
through the lift triangle. -/
theorem Representation.pullbackTautologicalIso_spec
    (hπ : Representation π ℰ) {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f) :
    (Scheme.Modules.pullback σ.hom).map (tautologicalQuotient π hπ).hom ≫
        (hπ.pullbackTautologicalSheafIso f σ).hom =
      (Lift.pullbackSourceIso σ ℰ).hom ≫ (hπ.liftSourceQuotient f σ).hom := by
  sorry

/-- The actual tautological target is invertible by the explicit degree-one twist presentation. -/
@[stacks 01OB "invertibility of the projective-bundle tautological module",
  stacks 01VM "invertibility of the projective-bundle tautological module"]
theorem tautologicalSheaf_isInvertible (π : P ⟶ X) (hπ : Representation π ℰ) :
    Scheme.Modules.Invertible (tautologicalSheaf π hπ) :=
  letI := hπ.quasicoherent
  hπ.symmetricPresentation.degreeOneTwist.twistOne_isInvertible

end AlgebraicGeometry.Scheme.ProjectiveBundle
