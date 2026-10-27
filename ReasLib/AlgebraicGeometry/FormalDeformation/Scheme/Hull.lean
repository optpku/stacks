/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme.Projection
public import ReasLib.AlgebraicGeometry.FormalDeformation.Prorepresentable
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothFunctor
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber
public import ReasLib.CategoryTheory.Cofibered.FiberIsoClass
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Hulls and prorepresentability for deformations of proper schemes

Over a classical complete local base, the functor of isomorphism classes of
deformations of a proper scheme has a hull. It is prorepresentable when the
scheme has vanishing global derivations over the residue field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

noncomputable section

universe u

namespace FlatSchemeCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))

/-- The functor sending an Artinian local algebra to the isomorphism classes of
deformations of a scheme over that algebra. -/
abbrev isoClassFunctor : ArtinianLocalAlgCat Λ k ⥤ Type (u + 1) :=
  fiberIsoClassFunctor (deformationForget Λ k X hX)

/-- Over a classical complete local base, the functor of isomorphism classes of
deformations of a proper scheme has a hull: a smooth transformation from a
prorepresentable functor that is bijective on dual-number points. -/
theorem isoClassFunctor_exists_isHull [IsProper hX] [ArtinianLocalAlgCat.IsClassical Λ k] :
    ∃ R : CompleteLocalAlgCat Λ k,
      ∃ η : CompleteLocalAlgCat.restrictedCoyoneda R ⋙ uliftFunctor.{u + 1, u} ⟶
          isoClassFunctor Λ k X hX,
        NatTrans.IsSmooth η ∧
          Function.Bijective (η.app (ArtinianLocalAlgCat.dualNumber Λ k)) :=
  sorry

/-- Over a classical complete local base, the functor of isomorphism classes of
deformations of a proper scheme is prorepresentable if the scheme has vanishing
global derivations over the residue field. -/
theorem isoClassFunctor_isProrepresentable [IsProper hX]
    [ArtinianLocalAlgCat.IsClassical Λ k]
    (h_der : Subsingleton
      (AlgebraicGeometry.RingedSpace.Hom.derivations hX.toShHom
        (SheafOfModules.unit X.toRingedSpace.ringCatSheaf))) :
    ∃ R : CompleteLocalAlgCat Λ k,
      Nonempty
        ((CompleteLocalAlgCat.restrictedCoyoneda R ⋙ uliftFunctor.{u + 1, u}) ≅
          isoClassFunctor Λ k X hX) :=
  sorry

end FlatSchemeCat
