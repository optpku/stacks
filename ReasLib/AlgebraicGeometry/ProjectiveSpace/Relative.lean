/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative projective spaces

This file provides the reusable abstract model of relative projective space used when a concrete
relative `Proj` construction is not fixed.  Its defining datum is a projective-bundle structure
for the standard finite free module.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpaceOver

/-- The standard free rank-`n + 1` module used to model relative projective `n`-space over `S`. -/
@[stacks 01OE "standard module for relative projective space"]
abbrev standardModule (S : Scheme.{u}) (n : ℕ) : S.Modules :=
  SheafOfModules.freeFin (n + 1)

end ProjectiveSpaceOver

/-- A chosen model of relative projective `n`-space over a scheme `S`. -/
@[stacks 01NF "relative projective space"]
structure ProjectiveSpaceOver (S : Scheme.{u}) (n : ℕ) where
  /-- The underlying scheme. -/
  scheme : Scheme.{u}
  /-- The structure morphism to the base. -/
  hom : scheme ⟶ S
  /-- The projective-bundle structure for the standard free module. -/
  isProjectiveBundle :
    Scheme.ProjectiveBundle.Representation hom (ProjectiveSpaceOver.standardModule S n)

/-- Packages a scheme over `S` together with its projective-bundle representation as a chosen
relative projective `n`-space. -/
def ProjectiveSpaceOver.ofRepresentation {S : Scheme.{u}} {n : ℕ} (P : Scheme.{u})
    (π : P ⟶ S)
    (hπ : Scheme.ProjectiveBundle.Representation π (ProjectiveSpaceOver.standardModule S n)) :
    ProjectiveSpaceOver S n :=
  ⟨P, π, hπ⟩

/-- The tautological module on a chosen relative projective space, obtained from its canonical
identity quotient. -/
@[stacks 01VM "tautological module on relative projective space"]
noncomputable abbrev ProjectiveSpaceOver.tautologicalSheaf
    {S : Scheme.{u}} {n : ℕ} (P : ProjectiveSpaceOver S n) : P.scheme.Modules :=
  Scheme.ProjectiveBundle.tautologicalSheaf P.hom P.isProjectiveBundle

/-- The tautological module on a chosen relative projective space is invertible. -/
@[stacks 01VM "invertibility of the relative projective-space tautological module"]
theorem ProjectiveSpaceOver.tautologicalSheaf_isInvertible
    {S : Scheme.{u}} {n : ℕ} (P : ProjectiveSpaceOver S n) :
    Scheme.Modules.Invertible P.tautologicalSheaf := sorry

end AlgebraicGeometry
