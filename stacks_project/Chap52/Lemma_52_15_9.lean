module

public import stacks_project.Chap52.Proposition_52_12_3
public import stacks_project.Chap52.Lemma_52_15_2_Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Opens

noncomputable section

universe u

set_option allowUnsafeReducibility true in
-- Local declaration justification (localized automation): unfold `Scheme.Opens.toScheme` so typeclass search finds the canonical Noetherian open-restriction instance.
attribute [local reducible] AlgebraicGeometry.Scheme.Opens.toScheme

namespace AlgebraicGeometry.AffineAlgebraizationSetup

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- Lemma 52.15.9: let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let
`U = Spec(A) ∖ V(𝔞)`, and let `F` and `G` be coherent modules on an open
neighborhood `V` of `U ∩ V(I)`. If `A` is `I`-adically complete, admits a
dualizing complex, and the closure of each associated point of `F` satisfies the
stated dimension bound along `V(𝔞)`, then the canonical germ-of-morphisms
comparison is bijective. Sections of `internalHom G.obj F.obj` over refinements of
`V` canonically represent the source morphisms, while its completion-side limit is
the established canonical view of morphisms from the completion of `G` to that of
`F`. -/
@[stacks 0EIV]
theorem neighborhoodHomComparison_bijective_of_associatedPointDimension
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (S : AffineAlgebraizationSetup A)
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
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
                    ((PointClosure.scheme ((V.val.ι ≫ S.U.ι) x)).presheaf.stalk z))) :
    Function.Bijective
      (Scheme.CoherentCompletion.neighborhoodComparison
        ((idealOnOpen S).comap V.val.ι)
        (Scheme.Modules.internalHom G.obj F.obj)) := sorry

end AlgebraicGeometry.AffineAlgebraizationSetup
