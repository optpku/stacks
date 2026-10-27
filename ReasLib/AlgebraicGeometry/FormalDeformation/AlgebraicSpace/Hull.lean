/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.AlgebraicSpace.RimSchlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.Prorepresentable
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothFunctor
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber
public import ReasLib.CategoryTheory.Cofibered.FiberIsoClass
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials

/-!
# Hulls and prorepresentability for deformations of proper algebraic spaces

Over a classical complete local base, the functor of isomorphism classes of
deformations of a proper algebraic space has a hull. Vanishing derivations imply
that this functor is prorepresentable.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Functor

noncomputable section

universe u

namespace FlatAlgebraicSpaceCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (X : AlgebraicSpace (Spec (CommRingCat.of k)))

/-- The functor sending an Artinian local algebra to the isomorphism classes of
deformations of an algebraic space over that algebra. -/
abbrev isoClassFunctor : ArtinianLocalAlgCat Λ k ⥤ Type (u + 1) :=
  fiberIsoClassFunctor (deformationForget Λ k X)

/-- Over a classical complete local base, the functor of isomorphism classes of
deformations of a proper algebraic space has a hull: a smooth transformation from
a prorepresentable functor that is bijective on dual-number points. -/
theorem exists_isHull_isoClass
    [AlgebraicSpace.Proper (AlgebraicGeometry.AlgebraicSpace.SchemeRealization.toBase X)]
    [ArtinianLocalAlgCat.IsClassical Λ k] :
    ∃ R : CompleteLocalAlgCat Λ k,
      ∃ η : CompleteLocalAlgCat.restrictedCoyoneda R ⋙ uliftFunctor.{u + 1, u} ⟶
          isoClassFunctor Λ k X,
        NatTrans.IsSmooth η ∧
          Function.Bijective (η.app (ArtinianLocalAlgCat.dualNumber Λ k)) := sorry

/-- Over a classical complete local base, the functor of isomorphism classes of
deformations of a proper algebraic space is prorepresentable if its residue
structure morphism has vanishing derivations with structure-module coefficients. -/
theorem isProrepresentable_isoClass
    [AlgebraicSpace.Proper (AlgebraicGeometry.AlgebraicSpace.SchemeRealization.toBase X)]
    [ArtinianLocalAlgCat.IsClassical Λ k]
    (h_der : Subsingleton
      (AlgebraicGeometry.AlgebraicSpace.Hom.derivations
        (ofResidue Λ k X).structureHom
        (SheafOfModules.unit (structureSheaf (ofResidue Λ k X).space)))) :
    ∃ R : CompleteLocalAlgCat Λ k,
      Nonempty
        (CompleteLocalAlgCat.restrictedCoyoneda R ⋙ uliftFunctor.{u + 1, u} ≅
          isoClassFunctor Λ k X) := sorry

end FlatAlgebraicSpaceCat
