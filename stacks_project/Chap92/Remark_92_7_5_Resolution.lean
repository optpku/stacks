/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.PolynomialTower.StandardResolution
import StacksCheckRecall

/-!
# Functorial standard resolutions and tensor base change

The standard resolutions over the initial ring give polynomial squares for an
injective tower map. Their tensor base changes resolve the target over the
intermediate ring.
-/

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialObject Algebra.PolynomialSite

noncomputable section

universe u

namespace RingedSite.Cotangent.PolynomialTriple

/-- The algebra structure on the intermediate ring induced by the first augmentation of a polynomial square. -/
@[reducible] def algebraPB {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (X : Algebra.PolynomialTower A B C) : Algebra X.P B :=
  X.toB.hom.toRingHom.toAlgebra

end RingedSite.Cotangent.PolynomialTriple

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/- Remark 92.7.5: the standard resolutions and their canonical functorial map. -/
@[stacks 08SD] #check (Algebra.CotangentComplex.standardP A B : SimplexCategoryᵒᵖ → Type u)
#check (Algebra.CotangentComplex.standardQ A C : SimplexCategoryᵒᵖ → Type u)
#check (Algebra.CotangentComplex.standardFunctoriality A B C :
  standardAugmented A B ⟶ standardAugmented A C)
#check (Algebra.CotangentComplex.tripleSimplicial A B C :
  Function.Injective (algebraMap B C) → SimplicialObject (Algebra.PolynomialTower A B C))
#check (Algebra.CotangentComplex.barQOver A B C :
  SimplexCategoryᵒᵖ → Function.Injective (algebraMap B C) → Algebra.PolynomialOver B C)
#check (Algebra.CotangentComplex.isResolution_barQHom A B C :
  ∀ h_inj : Function.Injective (algebraMap B C),
    IsResolution (Algebra.CotangentComplex.barQHom A B C h_inj))
