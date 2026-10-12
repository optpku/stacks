/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LinearSystem.Separation
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections

/-!
# Relative very ampleness from degree-two subschemes

This file records a criterion for relative very ampleness over an algebraically closed field in
terms of restrictions of sections to zero-dimensional subschemes of degree two.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- An invertible module on a proper scheme over an algebraically closed field is relatively very
ample if sections restrict surjectively to every zero-dimensional closed subscheme of degree two.
-/
theorem relativelyVeryAmple_of_degreeTwo_restriction_surjective
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (L : X.Modules) [Scheme.Modules.Invertible L]
    (hsurj :
      ∀ Z : X.IdealSheafData,
        topologicalKrullDim Z.subscheme = 0 →
          Module.finrank k (Scheme.Hom.globalSectionsAlg (Z.subschemeι ≫ f)) = 2 →
            Function.Surjective (Scheme.Modules.sectionsPullback Z.subschemeι L)) :
    RelativelyVeryAmple f L := sorry

end AlgebraicGeometry
