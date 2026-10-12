/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.ClosedImmersion

@[expose] public section

open CategoryTheory

universe u

section

variable {A B sigma tau : Type u} [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
  [CommRing B] [SetLike tau B] [AddSubgroupClass tau B]
  {calA : Nat → sigma} {calB : Nat → tau} [GradedRing calA] [GradedRing calB]
  (PcalA : AlgebraicGeometry.ProjTwistPresentation calA)
  (PcalB : AlgebraicGeometry.ProjTwistPresentation calB)
  (psi : calA →+*ᵍ calB)

/- Lemma 27.11.3: if the degreewise maps of `psi` are eventually surjective, then
`AlgebraicGeometry.projMapDomain psi = ⊤`, the induced map
`AlgebraicGeometry.Proj calB ⟶ AlgebraicGeometry.Proj calA` is a closed immersion, and every
integral-twist comparison is an epimorphism. These comparisons need not be isomorphisms, even
when the graded-ring map is surjective: for `A = k[x, y]` with `deg(x) = 1` and `deg(y) = 2`
and `B = k[y] = A / (x)`, the twist `𝒪_Y(1)` vanishes while the pullback of `𝒪_X(1)` does not. -/
@[stacks 01N0] #check
  (AlgebraicGeometry.projMapDomain_eq_top_of_eventually_surjective (psi := psi) :
    (∃ N : Nat, ∀ d : Nat, N ≤ d → Function.Surjective (psi.gradedAddHom d)) →
      AlgebraicGeometry.projMapDomain psi = ⊤)

#check
  (AlgebraicGeometry.projMap_isClosedImmersion_of_eventually_surjective
      (PcalA := PcalA) (PcalB := PcalB) (psi := psi) :
    (hpsisurj : ∃ N : Nat,
      ∀ d : Nat, N ≤ d → Function.Surjective (psi.gradedAddHom d)) →
      let hU : AlgebraicGeometry.projMapDomain psi = ⊤ :=
        AlgebraicGeometry.projMapDomain_eq_top_of_eventually_surjective hpsisurj
      AlgebraicGeometry.IsClosedImmersion
        (AlgebraicGeometry.projMapOnTarget psi
          (AlgebraicGeometry.projMap PcalA PcalB psi).map hU))

#check
  (AlgebraicGeometry.projMap_theta_epi_of_eventually_surjective
      (PcalA := PcalA) (PcalB := PcalB) (psi := psi) :
    (hpsisurj : ∃ N : Nat,
      ∀ d : Nat, N ≤ d → Function.Surjective (psi.gradedAddHom d)) →
      (n : Int) →
        let hU : AlgebraicGeometry.projMapDomain psi = ⊤ :=
          AlgebraicGeometry.projMapDomain_eq_top_of_eventually_surjective hpsisurj
        let hi : AlgebraicGeometry.projMapDomainTopInclusion psi hU ≫
            (AlgebraicGeometry.projMapDomain psi).ι = 𝟙 (AlgebraicGeometry.Proj calB) :=
          AlgebraicGeometry.projMapDomainTopInclusion_comp_ι psi hU
        CategoryTheory.Epi
          (AlgebraicGeometry.projMapThetaOnTarget psi
            (PcalA.actualTwist n) (PcalB.actualTwist n)
            (AlgebraicGeometry.projMap PcalA PcalB psi).map
            ((AlgebraicGeometry.projMap PcalA PcalB psi).theta n) hU hi))

end
