module

public import stacks_project.Chap52.«52_25_1_1_EulerCharacteristic»
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections.OverSpec

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.CoherentTriple

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {S : CoherentTripleSetup A}

/-- The canonical `A`-linear restriction map on sections for a coherent triple. -/
noncomputable def globalSectionsRestriction (L : CoherentTriple S) :
    Scheme.Hom.globalSectionsMod S.algebraization.U.ι L.F ⟶
      Scheme.Hom.globalSectionsMod
        (S.closedFiberOnU ≫ S.algebraization.U.ι)
        (L.F₀.restrict S.algebraization.U₀.ι) :=
  (Scheme.Modules.globalSectionsPullbackLinear S.algebraization.U.ι
      S.closedFiberOnU L.F) ≫
    (Scheme.Hom.globalSectionsFunctor
      (S.closedFiberOnU ≫ S.algebraization.U.ι)).map L.α.hom

/-- The section restriction map is the pullback-on-sections map followed by the map induced by
the coherent-triple comparison isomorphism. -/
theorem globalSectionsRestriction_def (L : CoherentTriple S) :
    L.globalSectionsRestriction =
      (Scheme.Modules.globalSectionsPullbackLinear S.algebraization.U.ι
        S.closedFiberOnU L.F) ≫
        (Scheme.Hom.globalSectionsFunctor
          (S.closedFiberOnU ≫ S.algebraization.U.ι)).map L.α.hom := sorry

end AlgebraicGeometry.CoherentTriple

