/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.RingTheory.RingHom.Fiber.FiniteType
import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.RelativeDualizing

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 47.25.5: for a flat finite-type algebra of Noetherian rings, all residue-field
fibres are Gorenstein if and only if its presentation-defined relative dualizing complex
is tensor-invertible in `D(A)`. -/
@[stacks 0E4C] #check
  (CategoryTheory.ModuleCat.UpperShriek.Presentation.fibersGorenstein_iff_relativeDualizingIsInvertible :
    ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
      [IsNoetherianRing R] [IsNoetherianRing A]
      [Algebra.FiniteType R A] [Module.Flat R A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} A))]
      (T : @CategoryTheory.DerivedCategory.DerivedTensor.Right.Monoidal.Model
        (ModuleCat.{u, u} A) _ _ _ _ _ _ _)
      (p : CategoryTheory.ModuleCat.UpperShriek.Presentation (algebraMap R A)),
      (∀ 𝓅 : PrimeSpectrum R, IsGorensteinRing (𝓅.asIdeal.Fiber A)) ↔
        MonoidalCategory.isInvertibleObject
          (p.functor.obj (ModuleCat.single0 (ModuleCat.of R R))))
