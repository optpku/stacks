module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ChosenPresentation
public import Mathlib.CategoryTheory.Sites.CoverLifting

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace AlgebraicGeometry.ChosenBigEtaleSite

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Realize a represented étale object as an object of the canonical small
étale site of the represented scheme. -/
def smallToEtale (S : Scheme.{u}) (X : ChosenBigEtaleSite.{u, v})
    (SX : X.carrier) (hX : X.toScheme.obj SX = S) :
    smallSite X SX ⥤ S.Etale where
  obj U := MorphismProperty.Over.mk (P := @Etale) (⊤ : MorphismProperty Scheme)
    (X.toScheme.map U.obj.hom ≫ eqToHom hX) (by
      have : Etale (X.toScheme.map U.obj.hom) := U.property
      infer_instance)
  map a := MorphismProperty.Over.homMk (X.toScheme.map a.hom.left) (by sorry)
  map_id := by sorry
  map_comp := by sorry

/-- Realization keeps the represented structural morphism, transported to `S`. -/
@[simp]
theorem smallToEtale_obj_hom (S : Scheme.{u})
    (X : ChosenBigEtaleSite.{u, v}) (SX : X.carrier)
    (hX : X.toScheme.obj SX = S) (U : smallSite X SX) :
    ((smallToEtale S X SX hX).obj U).hom =
      X.toScheme.map U.obj.hom ≫ eqToHom hX := rfl

/-- Realization acts on arrows by the given scheme functor. -/
@[simp]
theorem smallToEtale_map_left (S : Scheme.{u})
    (X : ChosenBigEtaleSite.{u, v}) (SX : X.carrier)
    (hX : X.toScheme.obj SX = S) {U V : smallSite X SX} (a : U ⟶ V) :
    ((smallToEtale S X SX hX).map a).left = X.toScheme.map a.hom.left := rfl

/-- Realization of a chosen small étale site is continuous. -/
instance smallToEtale_isContinuous (S : Scheme.{u})
    (X : ChosenBigEtaleSite.{u, v}) (SX : X.carrier)
    (hX : X.toScheme.obj SX = S) :
    (smallToEtale S X SX hX).IsContinuous (smallTopology X SX)
      S.smallEtaleTopology := sorry

/-- Realization of a chosen small étale site is cocontinuous. -/
instance smallToEtale_isCocontinuous (S : Scheme.{u})
    (X : ChosenBigEtaleSite.{u, v}) (SX : X.carrier)
    (hX : X.toScheme.obj SX = S) :
    (smallToEtale S X SX hX).IsCocontinuous (smallTopology X SX)
      S.smallEtaleTopology := sorry

/-- The canonical comparison between two presentations: right Kan extension
to the canonical small étale site, followed by restriction to the second
presentation. Both functors are defined on presheaves before imposing their
sheaf conditions. -/
def smallToposComparison (S : Scheme.{u})
    (X : ChosenBigEtaleSite.{u, v}) (Y : ChosenBigEtaleSite.{u, w})
    (SX : X.carrier) (SY : Y.carrier)
    (hX : X.toScheme.obj SX = S) (hY : Y.toScheme.obj SY = S) :
    Sheaf (smallTopology X SX) (Type (max u (max v w))) ⥤
      Sheaf (smallTopology Y SY) (Type (max u (max v w))) :=
  (smallToEtale S X SX hX).sheafPushforwardCocontinuous _
      (smallTopology X SX) S.smallEtaleTopology ⋙
    (smallToEtale S Y SY hY).sheafPushforwardContinuous _
      (smallTopology Y SY) S.smallEtaleTopology

/-- The presheaf underlying the comparison is the restriction of the right
Kan extension of the original presheaf. -/
@[simp]
theorem smallToposComparison_obj (S : Scheme.{u})
    (X : ChosenBigEtaleSite.{u, v}) (Y : ChosenBigEtaleSite.{u, w})
    (SX : X.carrier) (SY : Y.carrier)
    (hX : X.toScheme.obj SX = S) (hY : Y.toScheme.obj SY = S)
    (F : Sheaf (smallTopology X SX) (Type (max u (max v w)))) :
    ((smallToposComparison S X Y SX SY hX hY).obj F).obj =
      (smallToEtale S Y SY hY).op ⋙
        (smallToEtale S X SX hX).op.ran.obj F.obj := rfl

/-- The canonical comparison identifies the small étale topoi of two chosen
presentations of the same scheme. -/
theorem smallToposIndependent
    (S : Scheme.{u})
    (X : ChosenBigEtaleSite.{u, v}) (Y : ChosenBigEtaleSite.{u, w})
    (SX : X.carrier) (SY : Y.carrier)
    (hX : X.toScheme.obj SX = S) (hY : Y.toScheme.obj SY = S) :
    (smallToposComparison S X Y SX SY hX hY).IsEquivalence := sorry

end AlgebraicGeometry.ChosenBigEtaleSite
