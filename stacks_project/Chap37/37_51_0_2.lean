/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.ProjSpec.DerivedSections
public import stacks_project.Chap37.«37_51_0_1_ProjSpec»

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

open RingedSpace.Module.Derived Scheme.Hom.AbsoluteProjModel Scheme.Opens

namespace ProjSpec

/- 37.51.0.2: For a quasi-compact `P` and a quasi-coherent module `F` on `P`, the
derived sections of its pullback to `U` are isomorphic, over `A₀`, to the coproduct of
the derived sections of `F ⊗ 𝒪_P(m)` for `m : ℤ`. -/
@[stacks 0EKH] #check
  (AlgebraicGeometry.ProjSpec.derivedSectionsOpenIsomorphicCoproductTwists :
    (C : Construction) → [CompactSpace C.P] →
    (F : C.P.Modules) → [F.IsQuasicoherent] →
    IsIsomorphic
      ((ModuleCat.derivedRestrictionOfScalars
          (@Scheme.Hom.globalSectionsMap _ (degreeZeroRing C.A).commRing _
            (C.openToProj ≫ C.projToZero))).obj
        ((GlobalSections.functor (toScheme C.U).toRingedSpace).obj
          ((DerivedCategory.singleFunctor (toScheme C.U).toRingedSpace.Modules 0).obj
            ((Scheme.Modules.toRingedSpace C.U.toScheme).obj
              ((Scheme.Modules.pullback C.openToProj).obj F)))))
      (∐ fun m : ℤ ↦
        (ModuleCat.derivedRestrictionOfScalars
            (@Scheme.Hom.globalSectionsMap _ (degreeZeroRing C.A).commRing _ C.projToZero)).obj
          ((GlobalSections.functor C.P.toRingedSpace).obj
            ((DerivedCategory.singleFunctor
                (RingedSpace.Modules C.P.toRingedSpace) 0).obj
              ((Scheme.Modules.toRingedSpace C.P).obj
                (tensorObj F
                  (@ProjTwistAlgebra.actualTwist
                    (ring C.A) (grade C.A) (ring C.A).commRing (gradeSetLike C.A)
                    (gradeAddSubgroupClass C.A) (grading C.A) (grading_inst C.A)
                    C.twists m)))))))

end ProjSpec
end AlgebraicGeometry
