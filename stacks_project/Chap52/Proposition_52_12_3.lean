module

public import stacks_project.Chap52.Lemma_52_12_2
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- Proposition 52.12.3: let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let
`U = Spec(A) ∖ V(𝔞)`, and let `F` be coherent on `U`. Assume that `A` is
`I`-adically complete and has a dualizing complex. If the reduced closure of every
associated point of `F` meeting `V(I)` outside `V(𝔞)` has local dimension greater
than `cd(A, I) + 1` along `V(𝔞)`, then the canonical map from sections over
neighborhoods of `U ∩ V(I)` to the inverse limit of the global sections
`H⁰(U, F / I ^ (n + 1)F)` is bijective. -/
@[stacks 0EG2]
theorem globalNeighborhoodComparison_bijective_of_associatedPointDimension
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (S : AffineAlgebraizationSetup A)
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    [IsAdicComplete S.I A]
    (F : RingedSpace.Coh (S.U.toScheme).toRingedSpace)
    (h_dimension : ∀ x : S.U, x ∈ associatedPoints F.obj →
      S.U.ι x ∉ (idealSheafDataOfIdealOnSpec S.I).support →
        ¬ Set.range (PointClosure.ι (S.U.ι x)) ∩
            (idealSheafDataOfIdealOnSpec S.I).support ⊆ S.U.compl →
          ∀ z : PointClosure.scheme (S.U.ι x),
            PointClosure.ι (S.U.ι x) z ∈ S.U.compl →
              ((Ideal.LocalCohomology.dimension S.I
                  S.I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim
                    ((PointClosure.scheme (S.U.ι x)).presheaf.stalk z))) :
    Function.Bijective (globalNeighborhoodComparison S F.obj) := sorry

end AlgebraicGeometry.AffineAlgebraizationSetup
