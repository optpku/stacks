/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.FormalDeformation.SchemeMorphism.RimSchlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.Prorepresentable
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothFunctor
public import ReasLib.CategoryTheory.Cofibered.FiberIsoClass
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials

/-!
# Hulls and prorepresentability for morphisms of proper schemes

Over a classical complete local base, the functor of isomorphism classes of
deformations of a morphism of proper schemes has a hull. It is prorepresentable
when both schemes have vanishing global derivations over the residue field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace FlatSchemeMorphismCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The functor of isomorphism classes of deformations of a morphism of schemes,
allowing both its source and target to deform. -/
abbrev isoClassFunctor (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    ArtinianLocalAlgCat Λ k ⥤ Type (u + 1) :=
  fiberIsoClassFunctor (deformationForget Λ k X Y f hX hY hf)

/-- Over a classical complete local base, the functor of isomorphism classes of
deformations of a morphism of proper schemes has a hull: a smooth transformation
from a prorepresentable functor that is bijective on dual-number points. -/
theorem exists_isHull (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [IsProper hX] [IsProper hY] [ArtinianLocalAlgCat.IsClassical Λ k] :
    ∃ R : CompleteLocalAlgCat Λ k,
      ∃ η : CompleteLocalAlgCat.restrictedCoyoneda R ⋙ uliftFunctor.{u + 1, u} ⟶
          isoClassFunctor Λ k X Y f hX hY hf,
        NatTrans.IsSmooth η ∧
          Function.Bijective (η.app (ArtinianLocalAlgCat.dualNumber Λ k)) :=
  sorry

/-- Over a classical complete local base, the functor of isomorphism classes of
deformations of a morphism of proper schemes is prorepresentable if both schemes
have vanishing global derivations over the residue field. -/
theorem isProrepresentable_isoClass (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [IsProper hX] [IsProper hY] [ArtinianLocalAlgCat.IsClassical Λ k]
    (h_derX : Subsingleton
      (Hom.derivations hX.toShHom
        (SheafOfModules.unit X.toRingedSpace.ringCatSheaf)))
    (h_derY : Subsingleton
      (Hom.derivations hY.toShHom
        (SheafOfModules.unit Y.toRingedSpace.ringCatSheaf))) :
    ∃ R : CompleteLocalAlgCat Λ k,
      Nonempty
        (CompleteLocalAlgCat.restrictedCoyoneda R ⋙ uliftFunctor.{u + 1, u} ≅
          isoClassFunctor Λ k X Y f hX hY hf) :=
  sorry

end FlatSchemeMorphismCat
