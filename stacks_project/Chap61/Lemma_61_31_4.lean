/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Cohomology.ChangeOfUniverse
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.BigProetaleSite

universe u w

variable {X Y : BigProetaleSite.{u}}
variable (incl : X.carrier ⥤ Y.carrier) (e : incl ⋙ Y.toScheme ≅ X.toScheme)
variable (S : X.carrier)

section Cohomology

variable [HasSheafify (X.toGrothendieck.over S) AddCommGrpCat.{w}]
variable [HasSheafify (Y.toGrothendieck.over (incl.obj S)) AddCommGrpCat.{w}]
variable [IsGrothendieckAbelian (Sheaf (X.toGrothendieck.over S) AddCommGrpCat.{w})]
variable [IsGrothendieckAbelian
  (Sheaf (Y.toGrothendieck.over (incl.obj S)) AddCommGrpCat.{w})]
variable [HasInjectiveResolutions
  (Sheaf (Y.toGrothendieck.over (incl.obj S)) AddCommGrpCat.{w})]
variable [HasInjectiveResolutions
  (Sheaf (X.toGrothendieck.over S) AddCommGrpCat.{w})]
variable (p : ℕ) (U : Over S)
variable (F' : Sheaf (Y.toGrothendieck.over (incl.obj S)) AddCommGrpCat.{w})


/- Lemma 61.31.4. Restricting an abelian sheaf along a bounded big pro-étale
slice inclusion preserves its derived sections, and every abelian sheaf on the
smaller slice is the restriction of its canonical extension. -/
@[stacks 0F4T] #check (AlgebraicGeometry.BigProetaleSite.cohomology_restriction_isIsomorphic incl e S p U F' :
    CategoryTheory.IsIsomorphic
      (((siteAbelianSectionsFunctor (X.toGrothendieck.over S) U).rightDerived p).obj
        ((sliceAbelianRestriction incl e S).obj F'))
      (((siteAbelianSectionsFunctor (Y.toGrothendieck.over (incl.obj S))
        ((Over.post incl).obj U)).rightDerived p).obj F'))

#check (AlgebraicGeometry.BigProetaleSite.containedSliceInclusion_cohomology_restrict incl e S p U F' :
    (((sliceAbelianRestriction incl e S) ⋙
        siteAbelianSectionsFunctor (X.toGrothendieck.over S) U).rightDerived p).obj F' ≅
      ((siteAbelianSectionsFunctor (Y.toGrothendieck.over (incl.obj S))
        ((Over.post incl).obj U)).rightDerived p).obj F')

#check (AlgebraicGeometry.BigProetaleSite.containedSliceInclusion_cohomology_restrict_eq incl e S p U F' :
    containedSliceInclusion_cohomology_restrict incl e S p U F' =
      (@SiteAbelianSectionsDerived.derivedSectionsIso _ _ _ _
      (X.toGrothendieck.over S) (Y.toGrothendieck.over (incl.obj S))
      (Over.post (X := S) incl) (sliceInclusion_isContinuous incl e S)
      (sliceInclusion_isCocontinuous incl e S) inferInstance inferInstance
      inferInstance inferInstance inferInstance p U).app F')

end Cohomology

section Extension

variable [∀ P : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{w},
  (Over.post (X := S) incl).op.HasPointwiseRightKanExtension P]


variable (F : Sheaf (X.toGrothendieck.over S) AddCommGrpCat.{w})

#check (AlgebraicGeometry.BigProetaleSite.containedSliceInclusion_extension incl e S F :
    Sheaf (Y.toGrothendieck.over (incl.obj S)) AddCommGrpCat.{w})

#check (AlgebraicGeometry.BigProetaleSite.containedSliceInclusion_extension_eq incl e S F :
    containedSliceInclusion_extension incl e S F =
      (@Functor.sheafPushforwardCocontinuous _ _ _ _ (Over.post (X := S) incl)
        AddCommGrpCat.{w} _ (X.toGrothendieck.over S)
        (Y.toGrothendieck.over (incl.obj S)) (sliceInclusion_isCocontinuous incl e S)
        inferInstance).obj F)

#check (AlgebraicGeometry.BigProetaleSite.containedSliceInclusion_extension_restrict incl e S F :
    (sliceAbelianRestriction incl e S).obj
      (containedSliceInclusion_extension incl e S F) ≅ F)

#check (AlgebraicGeometry.BigProetaleSite.containedSliceInclusion_extension_restrict_eq incl e S F :
    containedSliceInclusion_extension_restrict incl e S F =
      @asIso _ _ _ _ ((sliceAbelianRestrictionExtensionAdjunction incl e S).counit.app F)
    (@Functor.FullyFaithful.sheafAdjunctionCocontinuous_counit_app_isIso _ _ _ _
      (X.toGrothendieck.over S) (Y.toGrothendieck.over (incl.obj S))
      (Over.post (X := S) incl) AddCommGrpCat.{w} _
      (Functor.FullyFaithful.over S incl (inclusionFullyFaithful incl e))
      (sliceInclusion_isContinuous incl e S) (sliceInclusion_isCocontinuous incl e S)
      inferInstance F))

end Extension
