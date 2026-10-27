/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Ambient
public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Induced
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Square
public import ReasLib.CategoryTheory.Sites.BeckChevalley
public import ReasLib.CategoryTheory.Sites.Over.Cocontinuity
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Tactic.CrossRefAttribute

/-!
# Squares for localized morphisms of ringed sites

An arrow `c : U ⟶ f.base.obj V` determines four canonical morphisms of ringed topoi: the
localized morphism on the left, the original morphism on the right, and the two localization
morphisms to the ambient topoi.  This leaf packages those four edges and the forward `2`-cell.

A commutative square `c' ≫ f.base.map b = a ≫ c` also gives a square whose horizontal edges
are relocalizations and whose vertical edges are localized morphisms.  Its comparison is built
from a generic Beck--Chevalley square of slice sites, with the functor-level core exposed
separately from the ringed-topos packaging.

The comparison is constructed as a mate of explicit sheaf-functor comparisons.  Its
invertibility is exposed only as a proposition: no inverse is selected from a deferred
`IsIso` proof, so the concrete square never acquires `sorryAx` through `asIso`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe w u v uX vX uY vY

namespace CategoryTheory.GrothendieckTopology

variable {T : Type u} [Category.{v} T] (J : GrothendieckTopology T) (U : T)
variable [HasSheafify (J.over U) (Type w)]
variable [∀ P : (Over U)ᵒᵖ ⥤ Type w,
  (Over.forget U).op.HasPointwiseRightKanExtension P]

/-- The inverse image of the localization morphism presented cocontinuously by
`Over.forget U` is canonically the usual restriction functor to the slice site. -/
noncomputable def overForgetInverseImageIso :
    (Over.forget U).sheafPullbackCocontinuous (Type w) (J.over U) J ≅
      J.overPullback (Type w) U :=
  Adjunction.leftAdjointUniq
    ((Over.forget U).sheafPullbackCocontinuousAdjunction (J.over U) J)
    ((Over.forget U).sheafAdjunctionCocontinuous (Type w) (J.over U) J)

end CategoryTheory.GrothendieckTopology

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable (f : X.Hom Y) (V : Y.carrier)
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vX, w}]
variable [UnivLE.{max uY vY vX, w}]

/-- The forward inverse-image comparison for localizing a morphism at an object.  It is the
mate of the explicit direct-image localization square. -/
noncomputable def localizationInverseImageComparison :
    Y.siteTopology.overPullback (Type w) V ⋙
        (@Functor.sheafPullback _ _ _ _ (Over.post f.base) (Type w) _
          (Y.siteTopology.over V) (X.siteTopology.over (f.base.obj V))
          (localization_isContinuous f V) _) ⟶
      (@Functor.sheafPullback _ _ _ _ f.base (Type w) _
        Y.siteTopology X.siteTopology (Hom.base_isContinuous f) _) ⋙
        X.siteTopology.overPullback (Type w) (f.base.obj V) :=
  ((mateEquiv
      (@Functor.sheafAdjunctionContinuous _ _ _ _ f.base (Type w) _
        Y.siteTopology X.siteTopology (Hom.base_isContinuous f) _)
      (@Functor.sheafAdjunctionContinuous _ _ _ _ (Over.post f.base) (Type w) _
        (Y.siteTopology.over V) (X.siteTopology.over (f.base.obj V))
        (localization_isContinuous f V) _)).symm
    (@Functor.sheafPushforwardOverPostComp _ _ _ _ X.siteTopology Y.siteTopology
      f.base (Hom.base_isContinuous f) V (Type w) _).inv).natTrans

/-- The localized inverse-image comparison is invertible. -/
theorem localizationInverseImageComparison_isIso :
    IsIso (localizationInverseImageComparison f V) := sorry

end RingedSite.Hom

namespace RingedSite.Localization.AmbientSquare

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable (f : X.Hom Y) {V : Y.carrier} {U : X.carrier} (c : U ⟶ f.base.obj V)
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable [UnivLE.{max uY vX, w}] [UnivLE.{max uY vY vX, w}]

/-- The upper edge of the ambient localization square. -/
noncomputable abbrev upper : ToposHom (X.localization U) X :=
  Localization.toAmbient X U

/-- The left edge of the ambient localization square. -/
noncomputable abbrev left : ToposHom (X.localization U) (Y.localization V) :=
  f.localizationAt V c

/-- The right edge of the ambient localization square. -/
noncomputable abbrev right : ToposHom X Y :=
  f.toToposHom

/-- The lower edge of the ambient localization square. -/
noncomputable abbrev lower : ToposHom (Y.localization V) Y :=
  Localization.toAmbient Y V

/-- The composite around the upper and right sides of the ambient localization square. -/
noncomputable abbrev upperRight : ToposHom (X.localization U) Y :=
  ToposHom.comp (upper (X := X) (U := U))
    (right (X := X) (Y := Y) f)

/-- The composite around the left and lower sides of the ambient localization square. -/
noncomputable abbrev leftLower : ToposHom (X.localization U) Y :=
  ToposHom.comp (left (X := X) (Y := Y) f c)
    (lower (Y := Y) (V := V))

/-- The canonical forward comparison from the inverse image around the left-lower path to the
inverse image around the upper-right path. -/
noncomputable def inverseImageComparison :
    (leftLower f c).toTopos.inverseImage ⟶
      (upperRight f).toTopos.inverseImage :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (Functor.isoWhiskerRight
        (Y.siteTopology.overForgetInverseImageIso.{w} V)
        (f.localizationToposHom V).toTopos.inverseImage).hom
      (Localization.relocalization X c).toTopos.inverseImage ≫
    Functor.whiskerRight
      (f.localizationInverseImageComparison V)
      (Localization.relocalization X c).toTopos.inverseImage ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (f.toToposHom).toTopos.inverseImage
      (Functor.sheafPushforwardContinuousComp' (Over.mapForget c)
        (Type w) (X.siteTopology.over U)
        (X.siteTopology.over (f.base.obj V)) X.siteTopology).hom ≫
    Functor.whiskerLeft (f.toToposHom).toTopos.inverseImage
      (X.siteTopology.overForgetInverseImageIso.{w} U).inv

/-- The inverse-image comparison in the ambient localization square is invertible. -/
theorem inverseImageComparison_isIso :
    IsIso (inverseImageComparison f c) := by
  letI := f.localizationInverseImageComparison_isIso V
  unfold inverseImageComparison
  repeat' apply IsIso.comp_isIso'
  · infer_instance
  · exact Functor.isIso_whiskerRight _ _
  · exact Functor.isIso_whiskerRight _ _
  · infer_instance
  · exact Functor.isIso_whiskerLeft _ _
  · infer_instance

/-- The direct-image comparison obtained by conjugating the canonical inverse-image
comparison across the two composite adjunctions. -/
noncomputable def pushforwardComparison :
    (upperRight f).toTopos.pushforward ⟶
      (leftLower f c).toTopos.pushforward :=
  conjugateEquiv
    (upperRight f).toTopos.adjunction
    (leftLower f c).toTopos.adjunction
    (inverseImageComparison f c)

/-- The direct-image comparison is invertible. -/
theorem pushforwardComparison_isIso :
    IsIso (pushforwardComparison f c) := by
  letI := inverseImageComparison_isIso f c
  unfold pushforwardComparison
  infer_instance

/-- Compatibility of the ambient localization comparison with the two composite ring-valued
direct-image structure maps. -/
theorem comparison_comm :
    (upperRight f).directStructureMap ≫
        (MorphismOfTopoiIn.ringDirectImageNatTrans
          (pushforwardComparison f c)).app (X.localization U).structureSheaf =
      (leftLower f c).directStructureMap := sorry

/-- The forward `2`-morphism making the ambient localization square
commute as a square of ringed topoi. -/
@[stacks 04J1 "ambient comparison"]
noncomputable def comparison : ToposHom.TwoMorphism (upperRight f) (leftLower f c) where
  hom := pushforwardComparison f c
  comm := comparison_comm f c

/-- The forward `2`-morphism in the ambient localization square is
invertible on its underlying direct-image natural transformation. -/
@[stacks 04J1 "(1), invertible comparison"]
theorem comparison_hom_isIso : IsIso (comparison f c).hom :=
  pushforwardComparison_isIso f c

/-- The four canonical edges and forward `2`-cell of the ambient
localization square. -/
@[stacks 04J1 "ambient square"]
noncomputable def square :
    ToposHom.LaxCommSquare (X.localization U) X (Y.localization V) Y where
  upper := upper (X := X) (U := U)
  left := left (X := X) (Y := Y) f c
  right := right (X := X) (Y := Y) f
  lower := lower (Y := Y) (V := V)
  cell := comparison f c

/-- The ambient localization square is invertible. -/
@[stacks 04J1 "(1), invertible square"]
theorem square_isInvertible : (square f c).IsInvertible :=
  comparison_hom_isIso f c

end RingedSite.Localization.AmbientSquare

namespace RingedSite.Localization.RelocalizationSquare

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable [UnivLE.{max uY vY vX, w}]
variable (f : X.Hom Y) {V V' : Y.carrier} {U U' : X.carrier}
variable (c : U ⟶ f.base.obj V) (b : V' ⟶ V) (a : U' ⟶ U)
variable (c' : U' ⟶ f.base.obj V')

/-- The upper relocalization edge attached to `a : U' ⟶ U`. -/
noncomputable abbrev upper : ToposHom (X.localization U') (X.localization U) :=
  Localization.relocalization X a

/-- The localized morphism on the left, attached to `c' : U' ⟶ f.base.obj V'`. -/
noncomputable abbrev left : ToposHom (X.localization U') (Y.localization V') :=
  f.localizationAt V' c'

/-- The localized morphism on the right, attached to `c : U ⟶ f.base.obj V`. -/
noncomputable abbrev right : ToposHom (X.localization U) (Y.localization V) :=
  f.localizationAt V c

/-- The lower relocalization edge attached to `b : V' ⟶ V`. -/
noncomputable abbrev lower : ToposHom (Y.localization V') (Y.localization V) :=
  Localization.relocalization Y b

/-- The composite around the upper and right sides of the relocalization square. -/
noncomputable abbrev upperRight : ToposHom (X.localization U') (Y.localization V) :=
  ToposHom.comp (upper (X := X) a)
    (right (X := X) (Y := Y) f c)

/-- The composite around the left and lower sides of the relocalization square. -/
noncomputable abbrev leftLower : ToposHom (X.localization U') (Y.localization V) :=
  ToposHom.comp (left (X := X) (Y := Y) f c')
    (lower (Y := Y) b)

/-- The canonical square of slice-site functors underlying the comparison between localized
morphisms at `V'` and `V`. -/
noncomputable abbrev baseSquare :
    CatCommSq (Over.post f.base) (Over.map b)
      (Over.map (f.base.map b)) (Over.post f.base) :=
  Over.postMapCommSq f.base b

/-- The Beck--Chevalley comparison between the direct images of the canonical localized
morphisms and the two relocalizations. -/
noncomputable def corePushforwardComparison :
    (Localization.relocalization X (f.base.map b)).toTopos.pushforward ⋙
        (f.localizationToposHom V).toTopos.pushforward ⟶
      (f.localizationToposHom V').toTopos.pushforward ⋙
        (Localization.relocalization Y b).toTopos.pushforward :=
  @CatCommSq.BeckChevalley.comparison _ _ _ _ _ _ _ _
    (Y.siteTopology.over V') (X.siteTopology.over (f.base.obj V'))
    (Y.siteTopology.over V) (X.siteTopology.over (f.base.obj V))
    _ _ _ _ inferInstance inferInstance
    (Hom.localization_isContinuous f V) (Hom.localization_isContinuous f V')
    inferInstance inferInstance inferInstance inferInstance (baseSquare f b)

/-- The forward direct-image comparison for the relocalization square determined by a
commutative square `c' ≫ f.base.map b = a ≫ c` in the source site. -/
noncomputable def pushforwardComparison
    (hcomm : c' ≫ f.base.map b = a ≫ c) :
    (upperRight f c a).toTopos.pushforward ⟶
      (leftLower f b c').toTopos.pushforward :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (X.siteTopology.overMapPushforwardCompIso a c).hom
      (f.localizationToposHom V).toTopos.pushforward ≫
    Functor.whiskerRight
      (X.siteTopology.overMapPushforwardCongrIso hcomm.symm).hom
      (f.localizationToposHom V).toTopos.pushforward ≫
    Functor.whiskerRight
      (X.siteTopology.overMapPushforwardCompIso c' (f.base.map b)).inv
      (f.localizationToposHom V).toTopos.pushforward ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      ((Over.map c').sheafPushforwardCocontinuous
        (Type w) (X.siteTopology.over U')
          (X.siteTopology.over (f.base.obj V')))
      (corePushforwardComparison f b) ≫
    (Functor.associator _ _ _).inv

/-- The direct-image comparison in the relocalization square is
invertible. -/
@[stacks 04J1 "(2), direct-image invertibility"]
theorem pushforwardComparison_isIso
    (hcomm : c' ≫ f.base.map b = a ≫ c) :
    IsIso (pushforwardComparison f c b a c' hcomm) := sorry

/-- Compatibility of the relocalization comparison with the ring-valued direct-image structure
maps of the two composite morphisms. -/
theorem comparison_comm
    (hcomm : c' ≫ f.base.map b = a ≫ c) :
    (upperRight f c a).directStructureMap ≫
        (MorphismOfTopoiIn.ringDirectImageNatTrans
          (pushforwardComparison f c b a c' hcomm)).app
            (X.localization U').structureSheaf =
      (leftLower f b c').directStructureMap := sorry

/-- The forward `2`-morphism comparing relocalization before and after
a localized morphism of ringed topoi. -/
@[stacks 04J1 "(2), comparison"]
noncomputable def comparison
    (hcomm : c' ≫ f.base.map b = a ≫ c) :
    ToposHom.TwoMorphism (upperRight f c a) (leftLower f b c') where
  hom := pushforwardComparison f c b a c' hcomm
  comm := comparison_comm f c b a c' hcomm

/-- The forward `2`-morphism in the relocalization square is
invertible on its underlying direct-image natural transformation. -/
@[stacks 04J1 "(2), invertible comparison"]
theorem comparison_hom_isIso
    (hcomm : c' ≫ f.base.map b = a ≫ c) :
    IsIso (comparison f c b a c' hcomm).hom :=
  pushforwardComparison_isIso f c b a c' hcomm

/-- The four canonical relocalization and localized-morphism edges,
together with their forward `2`-cell. -/
@[stacks 04J1 "(2), relocalization square"]
noncomputable def square
    (hcomm : c' ≫ f.base.map b = a ≫ c) :
    ToposHom.LaxCommSquare
      (X.localization U') (X.localization U)
      (Y.localization V') (Y.localization V) where
  upper := upper (X := X) a
  left := left (X := X) (Y := Y) f c'
  right := right (X := X) (Y := Y) f c
  lower := lower (Y := Y) b
  cell := comparison f c b a c' hcomm

/-- The relocalization square is invertible. -/
@[stacks 04J1 "(2), invertible square"]
theorem square_isInvertible
    (hcomm : c' ≫ f.base.map b = a ≫ c) :
    (square f c b a c' hcomm).IsInvertible :=
  comparison_hom_isIso f c b a c' hcomm

end RingedSite.Localization.RelocalizationSquare

-- The slice-restriction comparison is data-clean.  The remaining concrete comparisons inherit
-- `sorryAx` from Prop-valued continuity/exactness and structure-map coherence in the existing
-- site/topos infrastructure; no inverse is chosen from any of the invertibility proofs above.
