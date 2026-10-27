/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChangeOfUniverse
public import ReasLib.CategoryTheory.Sites.Derived.SectionsComparison
public import ReasLib.CategoryTheory.Sites.FullyFaithful
public import Mathlib.CategoryTheory.IsomorphismClasses

@[expose] public section

noncomputable section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.BigProetaleSite

variable {X Y : BigProetaleSite.{u}}
variable (incl : X.carrier ⥤ Y.carrier) (e : incl ⋙ Y.toScheme ≅ X.toScheme)
variable (S : X.carrier)

/-- Restriction of abelian sheaves along a scheme-compatible bounded big pro-étale
slice inclusion. -/
abbrev sliceAbelianRestriction :
    Sheaf (Y.toGrothendieck.over (incl.obj S)) AddCommGrpCat.{w} ⥤
      Sheaf (X.toGrothendieck.over S) AddCommGrpCat.{w} :=
  @Functor.sheafPushforwardContinuous _ _ _ _ (Over.post (X := S) incl)
    AddCommGrpCat.{w} _ (X.toGrothendieck.over S)
    (Y.toGrothendieck.over (incl.obj S)) (sliceInclusion_isContinuous incl e S)

section Cohomology

variable [HasSheafify (X.toGrothendieck.over S) AddCommGrpCat.{w}]
variable [HasSheafify (Y.toGrothendieck.over (incl.obj S)) AddCommGrpCat.{w}]
variable [IsGrothendieckAbelian (Sheaf (X.toGrothendieck.over S) AddCommGrpCat.{w})]
variable [IsGrothendieckAbelian
  (Sheaf (Y.toGrothendieck.over (incl.obj S)) AddCommGrpCat.{w})]
variable [HasInjectiveResolutions
  (Sheaf (Y.toGrothendieck.over (incl.obj S)) AddCommGrpCat.{w})]
variable (p : ℕ) (U : Over S)
variable (F' : Sheaf (Y.toGrothendieck.over (incl.obj S)) AddCommGrpCat.{w})

/-- Right derivation of the composite restriction-and-sections functor agrees with
right-derived sections over the image object of a bounded big pro-étale slice inclusion. -/
def containedSliceInclusion_cohomology_restrict :
    (((sliceAbelianRestriction incl e S) ⋙
        siteAbelianSectionsFunctor (X.toGrothendieck.over S) U).rightDerived p).obj F' ≅
      ((siteAbelianSectionsFunctor (Y.toGrothendieck.over (incl.obj S))
        ((Over.post incl).obj U)).rightDerived p).obj F' :=
  (@SiteAbelianSectionsDerived.derivedSectionsIso _ _ _ _
      (X.toGrothendieck.over S) (Y.toGrothendieck.over (incl.obj S))
      (Over.post (X := S) incl) (sliceInclusion_isContinuous incl e S)
      (sliceInclusion_isCocontinuous incl e S) inferInstance inferInstance
      inferInstance inferInstance inferInstance p U).app F'

/-- The derived restriction comparison is the canonical derived sections comparison. -/
theorem containedSliceInclusion_cohomology_restrict_eq :
    containedSliceInclusion_cohomology_restrict incl e S p U F' =
      (@SiteAbelianSectionsDerived.derivedSectionsIso _ _ _ _
      (X.toGrothendieck.over S) (Y.toGrothendieck.over (incl.obj S))
      (Over.post (X := S) incl) (sliceInclusion_isContinuous incl e S)
      (sliceInclusion_isCocontinuous incl e S) inferInstance inferInstance
      inferInstance inferInstance inferInstance p U).app F' := rfl

variable [HasInjectiveResolutions
  (Sheaf (X.toGrothendieck.over S) AddCommGrpCat.{w})]

/-- Cohomology of an abelian sheaf restricted to a smaller bounded big pro-étale slice
is isomorphic to its cohomology over the image object in the larger slice. -/
theorem cohomology_restriction_isIsomorphic :
    CategoryTheory.IsIsomorphic
      (((siteAbelianSectionsFunctor (X.toGrothendieck.over S) U).rightDerived p).obj
        ((sliceAbelianRestriction incl e S).obj F'))
      (((siteAbelianSectionsFunctor (Y.toGrothendieck.over (incl.obj S))
        ((Over.post incl).obj U)).rightDerived p).obj F') :=
  sorry

end Cohomology

section Extension

variable [∀ P : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{w},
  (Over.post (X := S) incl).op.HasPointwiseRightKanExtension P]

/-- Extension of abelian sheaves along a bounded big pro-étale slice inclusion by
cocontinuous pushforward. -/
def sliceAbelianExtension :
    Sheaf (X.toGrothendieck.over S) AddCommGrpCat.{w} ⥤
      Sheaf (Y.toGrothendieck.over (incl.obj S)) AddCommGrpCat.{w} :=
  @Functor.sheafPushforwardCocontinuous _ _ _ _ (Over.post (X := S) incl)
    AddCommGrpCat.{w} _ (X.toGrothendieck.over S)
    (Y.toGrothendieck.over (incl.obj S)) (sliceInclusion_isCocontinuous incl e S)
    inferInstance

/-- Restriction is left adjoint to cocontinuous extension of abelian sheaves on
bounded big pro-étale slices. -/
def sliceAbelianRestrictionExtensionAdjunction :
    sliceAbelianRestriction incl e S ⊣ sliceAbelianExtension incl e S :=
  @Functor.sheafAdjunctionCocontinuous _ _ _ _ (Over.post (X := S) incl)
    AddCommGrpCat.{w} _ (X.toGrothendieck.over S)
    (Y.toGrothendieck.over (incl.obj S)) (sliceInclusion_isCocontinuous incl e S)
    inferInstance (sliceInclusion_isContinuous incl e S)

variable (F : Sheaf (X.toGrothendieck.over S) AddCommGrpCat.{w})

/-- The canonical extension of an abelian sheaf to a larger bounded big pro-étale slice. -/
def containedSliceInclusion_extension :
    Sheaf (Y.toGrothendieck.over (incl.obj S)) AddCommGrpCat.{w} :=
  (sliceAbelianExtension incl e S).obj F

/-- The canonical extension is the objectwise cocontinuous pushforward. -/
theorem containedSliceInclusion_extension_eq :
    containedSliceInclusion_extension incl e S F =
      (@Functor.sheafPushforwardCocontinuous _ _ _ _ (Over.post (X := S) incl)
        AddCommGrpCat.{w} _ (X.toGrothendieck.over S)
        (Y.toGrothendieck.over (incl.obj S)) (sliceInclusion_isCocontinuous incl e S)
        inferInstance).obj F := rfl

/-- Restricting the canonical extension of an abelian sheaf along a bounded big
pro-étale slice inclusion recovers that sheaf. The inverse is the limit lift whose
component at an arrow in the image of the inclusion is the corresponding restriction map. -/
def containedSliceInclusion_extension_restrict :
    (sliceAbelianRestriction incl e S).obj
      (containedSliceInclusion_extension incl e S F) ≅ F where
  hom := (sliceAbelianRestrictionExtensionAdjunction incl e S).counit.app F
  inv := ObjectProperty.homMk
    { app := fun U ↦
        ((Over.post (X := S) incl).op.isPointwiseRightKanExtensionRanCounit
          F.obj ((Over.post (X := S) incl).op.obj U)).lift
          { pt := F.obj.obj U
            π :=
              { app := fun j ↦ F.obj.map
                  ((Functor.FullyFaithful.over S incl (inclusionFullyFaithful incl e)).op.preimage
                    j.hom)
                naturality := by sorry } }
      naturality := by sorry }
  hom_inv_id := by sorry
  inv_hom_id := by sorry

/-- The extension-restriction isomorphism is the canonical cocontinuous adjunction counit. -/
theorem containedSliceInclusion_extension_restrict_eq :
    containedSliceInclusion_extension_restrict incl e S F =
      @asIso _ _ _ _ ((sliceAbelianRestrictionExtensionAdjunction incl e S).counit.app F)
    (@Functor.FullyFaithful.sheafAdjunctionCocontinuous_counit_app_isIso _ _ _ _
      (X.toGrothendieck.over S) (Y.toGrothendieck.over (incl.obj S))
      (Over.post (X := S) incl) AddCommGrpCat.{w} _
      (Functor.FullyFaithful.over S incl (inclusionFullyFaithful incl e))
      (sliceInclusion_isContinuous incl e S) (sliceInclusion_isCocontinuous incl e S)
      inferInstance F) := by
  apply Iso.ext
  rfl

end Extension

end AlgebraicGeometry.BigProetaleSite
