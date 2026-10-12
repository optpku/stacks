/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.ValuationRing
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpace Scheme.Hom Scheme.Modules

noncomputable section

universe u

/- Lemma 37.33.3: an invertible module on a proper flat finitely presented scheme over a
valuation ring is trivial if its generic-fiber pullback is trivial, its special fiber is
integral, and the canonical map from the generic-point residue field to generic-fiber global
functions is bijective. -/
@[stacks 0EX8] #check (
  AlgebraicGeometry.Scheme.Modules.Invertible.isTrivial_of_valuationRing :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
      [Flat f] [IsProper f] [FinitePresentation f]
      (L : X.Modules) [Invertible L]
      [IsIntegral (f.fiber (IsLocalRing.closedPoint R))]
      (h_generic_trivial :
        IsTrivial
          ((pullback
            (f.fiberι (genericPoint (Spec (CommRingCat.of R))))).obj L))
      (h_global_sections : Function.Bijective
        (globalSectionsMap
          (f.fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of R)))))),
      IsTrivial L)
