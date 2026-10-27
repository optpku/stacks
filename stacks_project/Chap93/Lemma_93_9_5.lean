/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme.Hull
import StacksCheckRecall

/-!
# Hulls and prorepresentability of isomorphism classes of scheme deformations

For a proper scheme over the residue field of a classical complete local base,
its functor of deformation isomorphism classes has a hull. If its global
relative derivations vanish, this functor is prorepresentable.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
variable [IsProper hX] [ArtinianLocalAlgCat.IsClassical Λ k]

/- Lemma 93.9.5 (1)
The functor of isomorphism classes of deformations of a proper scheme over the
residue field of a classical complete local base has a hull. -/
@[stacks 0ET5] #check (FlatSchemeCat.isoClassFunctor_exists_isHull Λ k X hX :
  ∃ R : CompleteLocalAlgCat Λ k,
    ∃ η : CompleteLocalAlgCat.restrictedCoyoneda R ⋙ uliftFunctor.{u + 1, u} ⟶
        FlatSchemeCat.isoClassFunctor Λ k X hX,
      NatTrans.IsSmooth η ∧
        Function.Bijective (η.app (ArtinianLocalAlgCat.dualNumber Λ k)))

/- Lemma 93.9.5 (2)
If the global relative derivations of the proper scheme vanish, the same
isomorphism-class functor is prorepresentable. -/
@[stacks 0ET5] #check (FlatSchemeCat.isoClassFunctor_isProrepresentable Λ k X hX :
  Subsingleton
      (AlgebraicGeometry.RingedSpace.Hom.derivations hX.toShHom
        (SheafOfModules.unit X.toRingedSpace.ringCatSheaf)) →
    ∃ R : CompleteLocalAlgCat Λ k,
      Nonempty
        ((CompleteLocalAlgCat.restrictedCoyoneda R ⋙ uliftFunctor.{u + 1, u}) ≅
          FlatSchemeCat.isoClassFunctor Λ k X hX))

#check (CategoryTheory.Functor.fiberIsoClassFunctor.obj
  (FlatSchemeCat.deformationForget Λ k X hX) :
  ∀ A : ArtinianLocalAlgCat Λ k,
    (FlatSchemeCat.isoClassFunctor Λ k X hX).obj A =
      isomorphismClasses.obj (Cat.of ((FlatSchemeCat.deformationForget Λ k X hX).Fiber A)))

