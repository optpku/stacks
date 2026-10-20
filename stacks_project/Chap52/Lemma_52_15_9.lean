module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.AssociatedPoints
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Opens

noncomputable section

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

/- Lemma 52.15.9: let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let
`U = Spec(A) ∖ V(𝔞)`, and let `F` and `G` be coherent modules on an open
neighborhood `V` of `U ∩ V(I)`. If `A` is `I`-adically complete, admits a
dualizing complex, and the closure of each associated point of `F` satisfies the
stated dimension bound along `V(𝔞)`, then the canonical germ-of-morphisms
comparison is bijective. Sections of `internalHom G.obj F.obj` over refinements of
`V` canonically represent the source morphisms, while its completion-side limit is
the established canonical view of morphisms from the completion of `G` to that of
`F`. -/
@[stacks 0EIV]
#check (AlgebraicGeometry.AffineAlgebraizationSetup.neighborhoodHomComparison_bijective_of_associatedPointDimension :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A)
    (h_dualizing : CategoryTheory.DerivedCategory.HasCanonicalDualizingComplex A)
    [IsAdicComplete S.I A]
    (V : OpenNeighborhoods S)
    (F G : RingedSpace.Coh (toScheme V.val).toRingedSpace)
    (h_dimension : ∀ x : V.val, x ∈ associatedPoints F.obj →
      (V.val.ι ≫ S.U.ι) x ∉ (idealSheafDataOfIdealOnSpec S.I).support →
        ¬ Set.range (PointClosure.ι ((V.val.ι ≫ S.U.ι) x)) ∩
            (idealSheafDataOfIdealOnSpec S.I).support ⊆ S.U.compl →
          ∀ z : PointClosure.scheme ((V.val.ι ≫ S.U.ι) x),
            PointClosure.ι ((V.val.ι ≫ S.U.ι) x) z ∈ S.U.compl →
              ((Ideal.LocalCohomology.dimension S.I
                  S.I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim
                    ((PointClosure.scheme ((V.val.ι ≫ S.U.ι) x)).presheaf.stalk z))),
    Function.Bijective
      (Scheme.CoherentCompletion.neighborhoodComparison
        ((idealOnOpen S).comap V.val.ι)
        (Scheme.Modules.internalHom G.obj F.obj)))

end AlgebraicGeometry.AffineAlgebraizationSetup
