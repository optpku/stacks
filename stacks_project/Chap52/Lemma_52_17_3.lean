/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Sections.Quotient
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/- Lemma 52.17.3 (1) -/
@[stacks 0EHG] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.restrictedSectionsQuotientSystem_isCoherent :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (S : AffineAlgebraizationSetup A)
      (F : CoherentFormalModules S.U.toScheme
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
      (h_topology : Functor.limitTopology (sectionsSystem S F) =
        Ideal.adicModuleTopology S.I (sectionsLimit S F)) (n : ℕ),
      ((restrictedSectionsQuotientSystem S F).obj (op n)).IsCoherent)

/- Lemma 52.17.3 (2) -/
@[stacks 0EHG] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.sectionsComparisonHom_mono :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (S : AffineAlgebraizationSetup A)
      (F : CoherentFormalModules S.U.toScheme
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
      (h_topology : Functor.limitTopology (sectionsSystem S F) =
        Ideal.adicModuleTopology S.I (sectionsLimit S F)),
      Mono (sectionsComparisonHom S F h_topology))

end AlgebraicGeometry.Scheme.CoherentFormalModules
