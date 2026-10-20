/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.AssociatedPoints
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

/- Proposition 52.12.6: for a Noetherian ring with `f ∈ 𝔞`, an `f`-adically
complete ring and a dualizing complex, the canonical comparison from sections
over neighborhoods to positive `f`-power quotient sections is bijective under
the stated associated-point and reduced-closure dimension condition. -/
@[stacks 0H49] #check
  (AlgebraicGeometry.AffineAlgebraizationSetup.globalNeighborhoodComparison_bijective_of_principal :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (𝔞 : Ideal A) (f : A) (hf : f ∈ 𝔞)
    (h_dualizing : CategoryTheory.DerivedCategory.HasCanonicalDualizingComplex A)
    [IsAdicComplete (Ideal.span {f}) A]
    (F : RingedSpace.Coh ((ofPrincipal 𝔞 f hf).U.toScheme).toRingedSpace)
    (h_dimension : ∀ x : (ofPrincipal 𝔞 f hf).U, x ∈ associatedPoints F.obj →
      (ofPrincipal 𝔞 f hf).U.ι x ∉
          (idealSheafDataOfIdealOnSpec (Ideal.span {f})).support →
        ¬ Set.range (PointClosure.ι ((ofPrincipal 𝔞 f hf).U.ι x)) ∩
            (idealSheafDataOfIdealOnSpec (Ideal.span {f})).support ⊆
          (ofPrincipal 𝔞 f hf).U.compl →
          ∀ z : PointClosure.scheme ((ofPrincipal 𝔞 f hf).U.ι x),
            PointClosure.ι ((ofPrincipal 𝔞 f hf).U.ι x) z ∈
                (ofPrincipal 𝔞 f hf).U.compl →
              (2 : WithBot ℕ∞) <
                ringKrullDim
                  ((PointClosure.scheme ((ofPrincipal 𝔞 f hf).U.ι x)).presheaf.stalk z)),
    Function.Bijective
      (globalNeighborhoodComparison (ofPrincipal 𝔞 f hf) F.obj))

end AlgebraicGeometry.AffineAlgebraizationSetup
