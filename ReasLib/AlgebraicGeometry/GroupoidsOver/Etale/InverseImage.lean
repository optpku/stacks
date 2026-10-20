module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.SheafComparison

/-!
# Inverse-image identification of small-étale restrictions

A 1-morphism `f : Y ⟶ X` of categories fibred in groupoids identifies the
small-étale restriction of `f⁻¹ F` at `y` with the small-étale restriction of
`F` at `f(y)`, after reindexing along `p(f(y)) = p(y)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor Opposite
open FiberedCategoryOver.Groupoids
open AlgebraicGeometry.Scheme
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {Y X : GroupoidsOver S} (f : Y ⟶ X)

/-- Scheme identification `p(f(y)) = p(y)` induced by commutativity of `f`. -/
theorem map_obj_left_eq (y : Y.total) :
    (X.p.obj ((toFunctor f).obj y)).left = (Y.p.obj y).left :=
  congrArg Over.left (Functor.congr_obj (comm f) y)

/-- The functor on small étale sites induced by `p(f(y)) = p(y)`. -/
def transportEtaleFunctor (y : Y.total) :
    (Y.p.obj y).left.Etale ⥤ (X.p.obj ((toFunctor f).obj y)).left.Etale :=
  (eqToIso (congrArg (fun U : Scheme.{u} => Cat.of U.Etale)
      (map_obj_left_eq f y).symm)).hom.toFunctor

/-- Transport of an étale neighborhood of `p(y)` to an étale neighborhood of
`p(f(y))` along `map_obj_left_eq`. -/
def transportEtale (y : Y.total) (V' : (Y.p.obj y).left.Etale) :
    (X.p.obj ((toFunctor f).obj y)).left.Etale :=
  (transportEtaleFunctor f y).obj V'

/-- Transport of morphisms of étale neighborhoods along `map_obj_left_eq`. -/
def transportEtale_map (y : Y.total) {V' W' : (Y.p.obj y).left.Etale} (i : V' ⟶ W') :
    transportEtale f y V' ⟶ transportEtale f y W' :=
  (transportEtaleFunctor f y).map i

/-- The object map of `transportEtaleFunctor` is `transportEtale`. -/
theorem transportEtaleFunctor_obj (y : Y.total) (V' : (Y.p.obj y).left.Etale) :
    (transportEtaleFunctor f y).obj V' = transportEtale f y V' :=
  rfl

/-- The cartesian lift of `x` along `V'` projects to `etaleOver x V'`. -/
private theorem smallEtaleEval_toBase_domain_eq {Z : GroupoidsOver S} (x : Z.total)
    (V' : (Z.p.obj x).left.Etale) :
    Z.p.obj ((smallEtaleEval x).obj V') = (etaleOver x V').left :=
  sorry

/-- Domain identification for the cartesian fill-in of `smallEtaleEval_map_app`. -/
private theorem smallEtaleEval_map_domain_eq (y : Y.total) (V' : (Y.p.obj y).left.Etale) :
    X.p.obj ((toFunctor f).obj ((smallEtaleEval y).obj V')) =
      (etaleOver ((toFunctor f).obj y) (transportEtale f y V')).left :=
  sorry

/-- Base morphism in `Over S` underlying `f` applied to the étale lift of `y`. -/
private def smallEtaleEval_map_base (y : Y.total) (V' : (Y.p.obj y).left.Etale) :
    X.p.obj ((smallEtaleEval y ⋙ toFunctor f).obj V') ⟶
      X.p.obj ((toFunctor f).obj y) :=
  X.p.map ((toFunctor f).map (smallEtaleEval_toBase y V'))

/-- The image of `smallEtaleEval_toBase y V'` under `f` and the cartesian lift of
`f(y)` lie over composable morphisms of `Over S`. -/
private theorem smallEtaleEval_map_app_comp (y : Y.total) (V' : (Y.p.obj y).left.Etale) :
    smallEtaleEval_map_base f y V' =
      eqToHom (smallEtaleEval_map_domain_eq f y V') ≫
        (etaleOver ((toFunctor f).obj y) (transportEtale f y V')).hom :=
  sorry

/-- The reverse triangle identity for the inverse cartesian fill-in. -/
private theorem smallEtaleEval_map_app_inv_comp (y : Y.total) (V' : (Y.p.obj y).left.Etale) :
    X.p.map (smallEtaleEval_toBase ((toFunctor f).obj y) (transportEtale f y V')) =
      eqToHom
        ((smallEtaleEval_toBase_domain_eq ((toFunctor f).obj y) (transportEtale f y V')).trans
          (smallEtaleEval_map_domain_eq f y V').symm) ≫
        smallEtaleEval_map_base f y V' :=
  sorry

/-- Cartesian fill-in comparing `f` applied to the étale lift of `y` with the
étale lift of `f(y)`, obtained from the universal property of
`smallEtaleEval_toBase (f(y))`. -/
def smallEtaleEval_map_app (y : Y.total) (V' : (Y.p.obj y).left.Etale) :
    (smallEtaleEval y ⋙ toFunctor f).obj V' ⟶
      (smallEtaleEval ((toFunctor f).obj y)).obj (transportEtale f y V') :=
  @IsStronglyCartesian.map _ _ _ _ X.p _ _ _ _
    (etaleOver ((toFunctor f).obj y) (transportEtale f y V')).hom
    (smallEtaleEval_toBase ((toFunctor f).obj y) (transportEtale f y V'))
    (Chosen.cartesianHom.isStronglyCartesian X.p
      (etaleOver ((toFunctor f).obj y) (transportEtale f y V')).hom
      ⟨(toFunctor f).obj y, rfl⟩) _ _
    (eqToHom (by exact smallEtaleEval_map_domain_eq f y V') :
      X.p.obj ((smallEtaleEval y ⋙ toFunctor f).obj V') ⟶
        (etaleOver ((toFunctor f).obj y) (transportEtale f y V')).left)
    (X.p.map ((toFunctor f).map (smallEtaleEval_toBase y V')))
    (by exact smallEtaleEval_map_app_comp f y V')
    ((toFunctor f).map (smallEtaleEval_toBase y V'))
    (IsHomLift.map X.p ((toFunctor f).map (smallEtaleEval_toBase y V')))

/-- Inverse cartesian fill-in of `smallEtaleEval_map_app`, obtained from the
universal property of the strongly cartesian image of
`smallEtaleEval_toBase y`. -/
def smallEtaleEval_map_app_inv (y : Y.total) (V' : (Y.p.obj y).left.Etale) :
    (smallEtaleEval ((toFunctor f).obj y)).obj (transportEtale f y V') ⟶
      (smallEtaleEval y ⋙ toFunctor f).obj V' :=
  @IsStronglyCartesian.map _ _ _ _ X.p _ _ _ _
    (X.p.map ((toFunctor f).map (smallEtaleEval_toBase y V')))
    ((toFunctor f).map (smallEtaleEval_toBase y V'))
    (IsFibered.isStronglyCartesian_of_isCartesian X.p
      (X.p.map ((toFunctor f).map (smallEtaleEval_toBase y V')))
      ((toFunctor f).map (smallEtaleEval_toBase y V'))) _ _
    (eqToHom (by
        exact (smallEtaleEval_toBase_domain_eq ((toFunctor f).obj y)
          (transportEtale f y V')).trans (smallEtaleEval_map_domain_eq f y V').symm) :
      X.p.obj ((smallEtaleEval ((toFunctor f).obj y)).obj (transportEtale f y V')) ⟶
        X.p.obj ((smallEtaleEval y ⋙ toFunctor f).obj V'))
    (X.p.map (smallEtaleEval_toBase ((toFunctor f).obj y) (transportEtale f y V')))
    (by exact smallEtaleEval_map_app_inv_comp f y V')
    (smallEtaleEval_toBase ((toFunctor f).obj y) (transportEtale f y V'))
    inferInstance

/-- Triangle identity for `smallEtaleEval_map_app` against the cartesian lift of
`f(y)`. -/
theorem smallEtaleEval_map_app_triangle (y : Y.total)
    (V' : (Y.p.obj y).left.Etale) :
    smallEtaleEval_map_app f y V' ≫
        smallEtaleEval_toBase ((toFunctor f).obj y) (transportEtale f y V') =
      (toFunctor f).map (smallEtaleEval_toBase y V') :=
  sorry

/-- Triangle identity for `smallEtaleEval_map_app_inv` against the image of the
cartesian lift of `y`. -/
theorem smallEtaleEval_map_app_inv_triangle (y : Y.total)
    (V' : (Y.p.obj y).left.Etale) :
    smallEtaleEval_map_app_inv f y V' ≫
        (toFunctor f).map (smallEtaleEval_toBase y V') =
      smallEtaleEval_toBase ((toFunctor f).obj y) (transportEtale f y V') :=
  sorry

/-- The forward cartesian comparison followed by the reverse comparison is the identity. -/
private theorem smallEtaleEval_map_app_hom_inv_id (y : Y.total)
    (V' : (Y.p.obj y).left.Etale) :
    smallEtaleEval_map_app f y V' ≫ smallEtaleEval_map_app_inv f y V' = 𝟙 _ :=
  sorry

/-- The reverse cartesian comparison followed by the forward comparison is the identity. -/
private theorem smallEtaleEval_map_app_inv_hom_id (y : Y.total)
    (V' : (Y.p.obj y).left.Etale) :
    smallEtaleEval_map_app_inv f y V' ≫ smallEtaleEval_map_app f y V' = 𝟙 _ :=
  sorry

/-- `smallEtaleEval_map_app` is an isomorphism of objects of the total category. -/
def smallEtaleEval_map_appIso (y : Y.total) (V' : (Y.p.obj y).left.Etale) :
    (smallEtaleEval y ⋙ toFunctor f).obj V' ≅
      (smallEtaleEval ((toFunctor f).obj y)).obj (transportEtale f y V') where
  hom := smallEtaleEval_map_app f y V'
  inv := smallEtaleEval_map_app_inv f y V'
  hom_inv_id := by exact smallEtaleEval_map_app_hom_inv_id f y V'
  inv_hom_id := by exact smallEtaleEval_map_app_inv_hom_id f y V'

/-- Naturality of `smallEtaleEval_map_app` in the étale neighborhood. -/
theorem smallEtaleEval_map_naturality (y : Y.total)
    {V' W' : (Y.p.obj y).left.Etale} (i : V' ⟶ W') :
    (smallEtaleEval y ⋙ toFunctor f).map i ≫ smallEtaleEval_map_app f y W' =
      smallEtaleEval_map_app f y V' ≫
        (smallEtaleEval ((toFunctor f).obj y)).map (transportEtale_map f y i) :=
  sorry

/-- Natural isomorphism identifying étale evaluation of `y` after `f` with étale
evaluation of `f(y)`. -/
def smallEtaleEval_map (y : Y.total) :
    smallEtaleEval y ⋙ toFunctor f ≅
      transportEtaleFunctor f y ⋙ smallEtaleEval ((toFunctor f).obj y) :=
  NatIso.ofComponents (fun V' ↦ smallEtaleEval_map_appIso f y V')
    (fun i ↦ smallEtaleEval_map_naturality f y i)

/-- The component of `smallEtaleEval_map` is `smallEtaleEval_map_app`. -/
theorem smallEtaleEval_map_hom_app (y : Y.total) (V' : (Y.p.obj y).left.Etale) :
    (smallEtaleEval_map f y).hom.app V' = smallEtaleEval_map_app f y V' :=
  rfl

variable [HasSheafify Y.etaleTopology (Type (u + 1))]
variable [HasWeakSheafify Y.etaleTopology (Type (u + 1))]
variable [HasWeakSheafify X.etaleTopology (Type (u + 1))]
variable [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1),
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]

/-- Restriction of `F` at `f(y)`, reindexed to the small étale site of `p(y)`. -/
def restrictSmallEtaleSheaf_reindex (y : Y.total)
    (F : Sheaf X.etaleTopology (Type (u + 1))) :
    Sheaf (Y.p.obj y).left.smallEtaleTopology (Type (u + 1)) where
  obj :=
    (transportEtaleFunctor f y).op ⋙ (restrictSmallEtaleSheaf F ((toFunctor f).obj y)).obj
  property := sorry

/-- The underlying presheaf of `restrictSmallEtaleSheaf_reindex` is reindexing of
`restrictSmallEtaleSheaf F (f(y))` along `transportEtaleFunctor`. -/
theorem restrictSmallEtaleSheaf_reindex_obj (y : Y.total)
    (F : Sheaf X.etaleTopology (Type (u + 1))) :
    (restrictSmallEtaleSheaf_reindex f y F).obj =
      (transportEtaleFunctor f y).op ⋙
        (restrictSmallEtaleSheaf F ((toFunctor f).obj y)).obj :=
  rfl

/-- Component isomorphism of the inverse-image restriction identification over an
étale neighborhood `V'`. -/
def restrictSmallEtaleSheaf_inverseImage_app (y : Y.total)
    (F : Sheaf X.etaleTopology (Type (u + 1))) (V' : (Y.p.obj y).left.Etale) :
    ((((toCartesianBasedFunctor f).morphismOfTopoiIn
            (StandardTopology.etale.overTopology S)).inverseImage.obj F).obj.obj
        (op ((smallEtaleEval y).obj V'))) ≅
      F.obj.obj
        (op ((smallEtaleEval ((toFunctor f).obj y)).obj (transportEtale f y V'))) :=
  (((Functor.isoWhiskerRight
      (CartesianBasedFunctor.morphismOfTopoiIn.inverseImageComparisonIso
        (toCartesianBasedFunctor f) (StandardTopology.etale.overTopology S))
      (sheafToPresheaf Y.etaleTopology (Type (u + 1)))).app F).app
        (op ((smallEtaleEval y).obj V')) ≪≫
    (toCartesianBasedFunctor f).toFunctor.sheafPushforwardContinuousObjObjIso (Type (u + 1))
      (J := Y.etaleTopology) (K := X.etaleTopology) F ((smallEtaleEval y).obj V')) ≪≫
    F.obj.mapIso (smallEtaleEval_map_appIso f y V').symm.op

/-- The forward component of the canonical inverse-image restriction identification. -/
def restrictSmallEtaleSheaf_inverseImage_app_hom (y : Y.total)
    (F : Sheaf X.etaleTopology (Type (u + 1))) (V' : (Y.p.obj y).left.Etale) :
    ((((toCartesianBasedFunctor f).morphismOfTopoiIn
            (StandardTopology.etale.overTopology S)).inverseImage.obj F).obj.obj
        (op ((smallEtaleEval y).obj V'))) ⟶
      F.obj.obj
        (op ((smallEtaleEval ((toFunctor f).obj y)).obj (transportEtale f y V'))) :=
  (restrictSmallEtaleSheaf_inverseImage_app f y F V').hom

/-- The inverse component of the canonical inverse-image restriction identification. -/
def restrictSmallEtaleSheaf_inverseImage_app_inv (y : Y.total)
    (F : Sheaf X.etaleTopology (Type (u + 1))) (V' : (Y.p.obj y).left.Etale) :
    F.obj.obj
        (op ((smallEtaleEval ((toFunctor f).obj y)).obj (transportEtale f y V'))) ⟶
      ((((toCartesianBasedFunctor f).morphismOfTopoiIn
            (StandardTopology.etale.overTopology S)).inverseImage.obj F).obj.obj
        (op ((smallEtaleEval y).obj V'))) :=
  (restrictSmallEtaleSheaf_inverseImage_app f y F V').inv

/-- Underlying presheaf isomorphism of the inverse-image restriction
identification. -/
def restrictSmallEtaleSheaf_inverseImage_presheaf (y : Y.total)
    (F : Sheaf X.etaleTopology (Type (u + 1))) :
    (restrictSmallEtaleSheaf
        (((toCartesianBasedFunctor f).morphismOfTopoiIn
            (StandardTopology.etale.overTopology S)).inverseImage.obj F)
        y).obj ≅
      (restrictSmallEtaleSheaf_reindex f y F).obj :=
  NatIso.ofComponents
    (fun V' ↦ restrictSmallEtaleSheaf_inverseImage_app f y F (unop V'))
    (fun _ ↦ sorry)

/-- Canonical identification `f⁻¹ F|_{U_étale} = F|_{U_étale}` of small étale
sheaves on `p(y)`. -/
def restrictSmallEtaleSheaf_inverseImage (y : Y.total)
    (F : Sheaf X.etaleTopology (Type (u + 1))) :
    restrictSmallEtaleSheaf
        (((toCartesianBasedFunctor f).morphismOfTopoiIn
            (StandardTopology.etale.overTopology S)).inverseImage.obj F)
        y ≅
      restrictSmallEtaleSheaf_reindex f y F :=
  ObjectProperty.isoMk _ (restrictSmallEtaleSheaf_inverseImage_presheaf f y F)

/-- On an étale neighborhood `V'`, the forward map of
`restrictSmallEtaleSheaf_inverseImage` is inverse-image evaluation followed by
`F` applied to the inverse cartesian fill-in. -/
theorem restrictSmallEtaleSheaf_inverseImage_hom_app (y : Y.total)
    (F : Sheaf X.etaleTopology (Type (u + 1))) (V' : (Y.p.obj y).left.Etale) :
    ((restrictSmallEtaleSheaf_inverseImage f y F).hom.hom.app (op V')) =
      restrictSmallEtaleSheaf_inverseImage_app_hom f y F V' :=
  rfl

end AlgebraicGeometry.GroupoidsOver
