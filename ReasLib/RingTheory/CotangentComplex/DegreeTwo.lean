/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Tor.Surjective
public import ReasLib.Algebra.PolynomialSite.Resolution
public import ReasLib.AlgebraicTopology.SimplicialObject.PolynomialAugmentation
public import ReasLib.AlgebraicGeometry.RingedSite.Cotangent.PolynomialSiteTor
public import ReasLib.RingTheory.CotangentComplex.Basic
public import ReasLib.RingTheory.Extension.Presentation.LengthTwo.Tor

/-!
# Degree-minus-two cotangent homology

A polynomial resolution computes degree-minus-two cotangent homology as a
kernel-Tor face cokernel. A polynomial presentation gives its explicit tensor
kernel model.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialObject
open Algebra Algebra.PolynomialSite
open CommAlgCat.Over.Polynomial.Site
open scoped Simplicial

noncomputable section

universe u

namespace Algebra.CotangentComplex

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The difference of the two degree-one kernel-Tor faces of a polynomial resolution. -/
def kernelTorFaceSub {P : SimplicialObject (CommAlgCat.{u} A)}
    (ε : P ⟶ (const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B)) [IsResolution ε] :
    kernelTorObj 1 ((asPolynomialSimplicial ε (IsResolution.isPolynomial (ε := ε))) _⦋1⦌) ⟶
      kernelTorObj 1 ((asPolynomialSimplicial ε (IsResolution.isPolynomial (ε := ε))) _⦋0⦌) :=
  kernelTorMap 1 ((asPolynomialSimplicial ε (IsResolution.isPolynomial (ε := ε))).δ
      (0 : Fin 2)) -
    kernelTorMap 1 ((asPolynomialSimplicial ε (IsResolution.isPolynomial (ε := ε))).δ
      (1 : Fin 2))

/-- Degree-minus-two cotangent homology is the kernel-Tor face cokernel of any resolution. -/
theorem cotangentHomology_negTwo_isIsomorphic_coker_faceSub
    {P : SimplicialObject (CommAlgCat.{u} A)}
    (ε : P ⟶ (const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B)) [IsResolution ε] :
    IsIsomorphic ((Algebra.cotangentComplex A B).homology (-2))
      (cokernel (kernelTorFaceSub ε)) := sorry

end Algebra.CotangentComplex

namespace Algebra.Presentation.LengthTwo

variable {A B ι σ : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The tensor-kernel face cokernel of a presentation is degree-minus-two cotangent homology. -/
theorem cokerFaceSub_isIsomorphic_cotangentHomology_negTwo (P : Presentation A B ι σ) :
    IsIsomorphic (cokerFaceSub P) ((Algebra.cotangentComplex A B).homology (-2)) := sorry

end Algebra.Presentation.LengthTwo
