/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatScheme
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Over

/-!
# Deformation slices of schemes
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

universe u

noncomputable section

namespace FlatSchemeCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- A scheme over the residue field determines a flat scheme over the residue algebra. -/
def ofResidue (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) : FlatSchemeCat Λ k :=
  FlatSchemeCat.of (Λ := Λ) (k := k) (ArtinianLocalAlgCat.residue Λ k) X hX
    (inferInstanceAs (AlgebraicGeometry.Flat hX))

/-- The base algebra of the residue pair is the residue algebra. -/
theorem ofResidue_base (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    (ofResidue Λ k X hX).base = ArtinianLocalAlgCat.residue Λ k := sorry

/-- A scheme over the residue field determines an object of the residue fibre. -/
def residueObj (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    (forget Λ k).Fiber (ArtinianLocalAlgCat.residue Λ k) :=
  Fiber.mk (rfl : (forget Λ k).obj (ofResidue Λ k X hX) = ArtinianLocalAlgCat.residue Λ k)

/-- The inclusion of the residue-fibre object is the residue pair. -/
theorem residueObj_fiberInclusion (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    Fiber.fiberInclusion.obj (residueObj Λ k X hX) = ofResidue Λ k X hX := sorry

/-- The deformation category of a scheme is the slice over its residue pair. -/
abbrev deformationCategory (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :=
  Over (Fiber.fiberInclusion.obj (residueObj Λ k X hX))

/-- The deformation category is the over category of the included residue-fibre object. -/
theorem deformationCategory_spec (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    deformationCategory Λ k X hX =
      Over (Fiber.fiberInclusion.obj (residueObj Λ k X hX)) := sorry

/-- The deformation slice projection of a scheme is a predeformation category. -/
instance instIsPredeformationCategory_deformationCategory
    (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    IsPredeformationCategory
      (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X hX)) ⋙ forget Λ k) :=
  instIsPredeformationCategory_overForget (forget Λ k) (residueObj Λ k X hX)

end FlatSchemeCat
