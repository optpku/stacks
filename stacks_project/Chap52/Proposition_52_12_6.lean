/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap52.Proposition_52_12_3
public import stacks_project.Chap52.Lemma_52_12_5_Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- Proposition 52.12.6: for a Noetherian ring with `f ∈ 𝔞`, an `f`-adically
complete ring and a dualizing complex, the canonical comparison from sections
over neighborhoods to positive `f`-power quotient sections is bijective under
the stated associated-point and reduced-closure dimension condition. -/
@[stacks 0H49]
theorem globalNeighborhoodComparison_bijective_of_principal
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (𝔞 : Ideal A) (f : A) (hf : f ∈ 𝔞)
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
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
                  ((PointClosure.scheme ((ofPrincipal 𝔞 f hf).U.ι x)).presheaf.stalk z)) :
    Function.Bijective
      (globalNeighborhoodComparison (ofPrincipal 𝔞 f hf) F.obj) := sorry

end AlgebraicGeometry.AffineAlgebraizationSetup
