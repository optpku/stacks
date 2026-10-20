module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.XyIdeal

/-!
# Non-finite global sections of a projective scheme
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- There exists a ring `R` and a projective scheme `X` over `R`
such that `Scheme.Hom.globalSectionsAlg` of `X ⟶ Spec R` is not a finite `R`-module. -/
theorem Projective.exists_globalSections_not_finite :
    ∃ (R : Type u) (_ : CommRing R) (X : Scheme.{u}) (f : X ⟶ Spec (.of R)),
      Projective f ∧ ¬ Module.Finite R (Scheme.Hom.globalSectionsAlg f) :=
  sorry

/-- There exists a ring `R` and a finite type quasi-coherent
module `F` on `P¹_R` such that `Scheme.Hom.globalSectionsMod` of `F` along
`P¹_R ⟶ Spec R` is not a finite `R`-module. -/
theorem ProjectiveSpace.exists_finiteTypeQuasicoherent_globalSections_not_finite :
    ∃ (R : Type u) (_ : CommRing R) (F : (ProjectiveSpace.scheme R 1).Modules),
      F.IsFiniteType ∧ F.IsQuasicoherent ∧
        ¬ Module.Finite R
            (Scheme.Hom.globalSectionsMod (ProjectiveSpace.toSpec R 1) F) :=
  sorry

end AlgebraicGeometry
