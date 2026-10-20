/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.DualNumber

/-!
# Trivial dual-number lift of an algebra deformation

The residue slice projection and the canonical trivial dual-number deformation.
-/

public section

open CategoryTheory Functor ArtinianLocalAlgCat

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

#check (FlatAlgebraCat.deformationForget Λ k :
  ∀ (P : Type u) [CommRing P] [Algebra k P],
    FlatAlgebraCat.deformationCategory Λ k P ⥤ ArtinianLocalAlgCat Λ k)
#check (FlatAlgebraCat.deformationForget_eq Λ k :
  ∀ (P : Type u) [CommRing P] [Algebra k P],
    FlatAlgebraCat.deformationForget Λ k P =
      Over.forget (Fiber.fiberInclusion.obj (FlatAlgebraCat.residueObj Λ k P)) ⋙
        FlatAlgebraCat.forget)
#check (FlatAlgebraCat.residueToDualNumber Λ k : residue Λ k ⟶ dualNumber Λ k)
#check (ArtinianLocalAlgCat.dualNumberToResidue Λ k : dualNumber Λ k ⟶ residue Λ k)
#check (FlatAlgebraCat.dualNumberRingHom Λ k :
  ∀ (P : Type u) [CommRing P] [Algebra k P], (dualNumber Λ k).carrier →+* DualNumber P)
#check (FlatAlgebraCat.trivialDeformationObj Λ k :
  ∀ (P : Type u) [CommRing P] [Algebra k P], FlatAlgebraCat Λ k)
#check (FlatAlgebraCat.trivialDeformation Λ k :
  ∀ (P : Type u) [CommRing P] [Algebra k P],
    (FlatAlgebraCat.forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k).Fiber
      (dualNumber Λ k))
#check (FlatAlgebraCat.trivialDeformationToResidue Λ k :
  ∀ (P : Type u) [CommRing P] [Algebra k P],
    FlatAlgebraCat.trivialDeformationObj Λ k P ⟶ FlatAlgebraCat.ofResidue Λ k P)
#check (FlatAlgebraCat.trivialPushforward Λ k :
  ∀ (P : Type u) [CommRing P] [Algebra k P],
    Fiber.fiberInclusion.obj (FlatAlgebraCat.residueObj Λ k P) ⟶
      Fiber.fiberInclusion.obj (FlatAlgebraCat.trivialDeformation Λ k P))
#check (FlatAlgebraCat.trivialDeformationOver Λ k :
  ∀ (P : Type u) [CommRing P] [Algebra k P], FlatAlgebraCat.deformationCategory Λ k P)
#check (FlatAlgebraCat.trivialDeformationFiber Λ k :
  ∀ (P : Type u) [CommRing P] [Algebra k P],
    (FlatAlgebraCat.deformationForget Λ k P).Fiber (dualNumber Λ k))
