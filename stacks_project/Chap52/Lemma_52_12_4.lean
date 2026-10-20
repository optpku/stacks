module

public import stacks_project.Chap52.Proposition_52_12_3
public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.AssociatedPoints
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

/- Lemma 52.12.4: let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let
`U = Spec(A) ∖ V(𝔞)`, and let `F` be coherent on `U`. Assume that `A` is
`I`-adically complete and has a dualizing complex. If the reduced closure of every
associated point of `F` meeting `V(I)` outside `V(𝔞)` has local dimension greater
than `cd(A, I) + 1` along `V(𝔞)`, and every point whose closure meets `V(I)` only
inside `V(𝔞)` has stalk depth at least two, then the canonical map from
`H⁰(U, F)` to the inverse limit of `H⁰(U, F / I ^ (n + 1)F)` is bijective. -/
@[stacks 0EIG] #check
  (AlgebraicGeometry.AffineAlgebraizationSetup.sectionsComparison_bijective_of_associatedPointDimension :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A)
    (h_dualizing : DerivedCategory.HasCanonicalDualizingComplex A)
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
                    ((PointClosure.scheme (S.U.ι x)).presheaf.stalk z)))
    (h_depth : ∀ x : S.U,
      Set.range (PointClosure.ι (S.U.ι x)) ∩
          (idealSheafDataOfIdealOnSpec S.I).support ⊆ S.U.compl →
        (2 : ℕ∞) ≤ moduleDepth ((S.U.toScheme).presheaf.stalk x)
          (RingedSpace.stalkModuleCat F.obj x)),
    Function.Bijective
      (Scheme.CoherentCompletion.sectionsComparison (idealOnOpen S) F.obj))

end AlgebraicGeometry.AffineAlgebraizationSetup
