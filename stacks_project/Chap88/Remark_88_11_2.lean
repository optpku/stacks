/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.RestrictedPowerSeries.NaiveCotangent.Homotopy
public import ReasLib.RingTheory.RestrictedPowerSeries.NaiveCotangent.Adic

/-!
# Remark 88.11.2

A restricted quotient presentation gives the conormal Jacobian complex in
homological degrees 1 and 0. Continuous presentation morphisms give its canonical
comparison in the homotopy category. Over a Noetherian adic coefficient ring,
the construction agrees with the ideal-adic complex and is independent of the
ideal of definition.

The construction itself needs no Noetherian hypothesis. In particular it also
applies to the arrows of countably indexed weakly admissible rings satisfying
the restricted quotient conditions described in the source footnote.
-/

@[expose] public section

open Algebra.NaiveCotangent
open Algebra.NaiveCotangent.Restricted
open CategoryTheory
open HomotopyCategory
open TopologicalRing
open TopologicalRing.Ideal

universe u

section Construction

variable {A B : Type u} [CommRing A] [TopologicalSpace A]
variable [IsTopologicalRing A] [IsLinearTopology A A] [CommRing B] [Algebra A B]
variable {ι : Type u} [Fintype ι]

#check (Algebra.NaiveCotangent.Restricted.naiveCotangent :
  Presentation A B ι → ChainComplex (ModuleCat B) ℕ)

end Construction

section PresentationIndependence

variable {A B : Type u} [CommRing A] [TopologicalSpace A]
variable [CommRing B] [TopologicalSpace B] [Algebra A B]
variable [IsAdicStarRing A] [IsAdicStarRing B]
variable {ι ι' : Type u} [Fintype ι] [Fintype ι']

/- Remark 88.11.2: The restricted Jacobian complex is well defined by the unique
comparison induced by continuous morphisms of topological quotient presentations. -/
@[stacks 0GBX] #check (Algebra.NaiveCotangent.Restricted.isoUnique :
  ∀ (hφ : Continuous (algebraMap A B))
    (h_adic : (algebraMap A B).IsAdicHom)
    (h_tft : (algebraMap A B).TopologicallyOfFiniteType)
    (P : Presentation A B ι) (Q : Presentation A B ι')
    (hP : P.IsTopological) (hQ : Q.IsTopological),
    ∃! e :
      (quotient (ModuleCat B) (ComplexShape.down ℕ)).obj (naiveCotangent P) ≅
        (quotient (ModuleCat B) (ComplexShape.down ℕ)).obj (naiveCotangent Q),
      ∀ f : Presentation.Hom P Q, e.hom = mapNaiveCotangent f)

variable [IsNoetherianRing A]

section AdicComparison

variable (I : Ideal A) (hI : IsIdealOfDefinition I) (P : Presentation A B ι)

#check (Algebra.NaiveCotangent.Restricted.complexIso_toAdic ι I hI P :
  naiveCotangent P ≅ Adic.naiveCotangent I (Presentation.toAdic ι I hI P))

end AdicComparison

#check (Algebra.NaiveCotangent.Restricted.independentOfIdeal :
  ∀ (hφ : Continuous (algebraMap A B))
    (h_adic : (algebraMap A B).IsAdicHom)
    (h_tft : (algebraMap A B).TopologicallyOfFiniteType)
    (I I' : Ideal A) (hI : IsIdealOfDefinition I) (hI' : IsIdealOfDefinition I')
    (P_adic : Adic.Presentation A B I ι)
    (Q_adic : Adic.Presentation A B I' ι'),
    Nonempty
      ((quotient (ModuleCat B) (ComplexShape.down ℕ)).obj
          (Adic.naiveCotangent I P_adic) ≅
        (quotient (ModuleCat B) (ComplexShape.down ℕ)).obj
          (Adic.naiveCotangent I' Q_adic)))

end PresentationIndependence
