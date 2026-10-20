/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.ProjSpec
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Coproducts

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

open RingedSpace.Module.Derived Scheme.Hom.AbsoluteProjModel Scheme.Opens

namespace ProjSpec

/-- For a quasi-compact projective spectrum and a quasi-coherent module `F`, the
derived sections of its pullback to the punctured spectrum are isomorphic, over
the degree-zero ring, to the coproduct of the derived sections of `F` tensored
with every integral twist. -/
theorem derivedSectionsOpenIsomorphicCoproductTwists
    (C : Construction) [CompactSpace C.P]
    (F : C.P.Modules) [F.IsQuasicoherent] :
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
                    C.twists m)))))) := sorry

end ProjSpec
end AlgebraicGeometry
