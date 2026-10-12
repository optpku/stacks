/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.SmallAffine
public import stacks_project.Chap96.Definition_96_12_1_Restriction
public import stacks_project.Chap96.Lemma_96_25_1_Module

/-!
# Affine étale restriction of modules on `𝒳_affine`

An object `x` of `𝒳_affine` determines a functor from the small affine étale
site of `U = p(x)` into `𝒳_affine`, by cartesian lifts of affine étale
neighbourhoods. Pushing an `𝒪`-module on `𝒳_affine` along the induced
comparison of structure sheaves yields the restriction
`x* F|_{U_affine,étale}`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.Functor
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- An affine étale neighbourhood of `U = p(x)` lifts to an affine object of
`X`, since the cartesian lift lies over the spectrum of the neighbourhood. -/
theorem smallAffineEtaleToAffine_obj_isAffine {X : GroupoidsOver S}
    (x : Affine X) (V : (X.p.obj x.obj).left.AffineEtale) :
    IsAffine
      (X.p.obj
          ((smallEtaleToTotal x.obj).obj
            ((AffineEtale.Spec (X.p.obj x.obj).left).obj V))).left :=
  sorry

/-- The functor from the small affine étale site of `U = p(x)` to `𝒳_affine`,
sending an affine étale neighbourhood of `U` to the rebundled cartesian lift of
`x`. -/
def smallAffineEtaleToAffine {X : GroupoidsOver S} (x : Affine X) :
    (X.p.obj x.obj).left.AffineEtale ⥤ Affine X where
  obj V :=
    Affine.mk
      ((smallEtaleToTotal x.obj).obj
        ((AffineEtale.Spec (X.p.obj x.obj).left).obj V))
      (smallAffineEtaleToAffine_obj_isAffine x V)
  map f :=
    InducedCategory.homMk
      ((smallEtaleToTotal x.obj).map
        ((AffineEtale.Spec (X.p.obj x.obj).left).map f))
  map_id _ := sorry
  map_comp _ _ := sorry

/-- `smallAffineEtaleToAffine x` is objectwise the rebundled cartesian lift of
`x` along `AffineEtale.Spec`. -/
theorem smallAffineEtaleToAffine_obj {X : GroupoidsOver S} (x : Affine X)
    (V : (X.p.obj x.obj).left.AffineEtale) :
    (smallAffineEtaleToAffine x).obj V =
      Affine.mk
        ((smallEtaleToTotal x.obj).obj
          ((AffineEtale.Spec (X.p.obj x.obj).left).obj V))
        (smallAffineEtaleToAffine_obj_isAffine x V) :=
  sorry

/-- The scheme-valued comparison from the image of `smallAffineEtaleToAffine x`
under `p` to the underlying scheme of an affine étale neighbourhood of
`U = p(x)`. -/
def smallAffineEtaleSchemeProjection {X : GroupoidsOver S} (x : Affine X) :
    smallAffineEtaleToAffine x ⋙ affineInclusion X ⋙ X.p ⋙ Over.forget S ⟶
      SmallStandardTopology.Affine.toOver .etale (X.p.obj x.obj).left ⋙
        Over.forget (X.p.obj x.obj).left where
  app V :=
    (smallEtaleSchemeProjection x.obj).app
      ((AffineEtale.Spec (X.p.obj x.obj).left).obj V)
  naturality := sorry

/-- The component of `smallAffineEtaleSchemeProjection` is the small-étale
scheme projection at the image of `AffineEtale.Spec`. -/
theorem smallAffineEtaleSchemeProjection_app {X : GroupoidsOver S}
    (x : Affine X) (V : (X.p.obj x.obj).left.AffineEtale) :
    (smallAffineEtaleSchemeProjection x).app V =
      (smallEtaleSchemeProjection x.obj).app
        ((AffineEtale.Spec (X.p.obj x.obj).left).obj V) :=
  sorry

/-- The universe-lifted commutative structure presheaf on the small affine étale
site of `U = p(x)`. -/
def smallAffineEtaleCommPresheaf {X : GroupoidsOver S} (x : Affine X) :
    ((X.p.obj x.obj).left.AffineEtale)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  Scheme.Over.commStructurePresheaf
    (SmallStandardTopology.Affine.toOver .etale (X.p.obj x.obj).left)

/-- Objectwise, `smallAffineEtaleCommPresheaf x` is the universe lift of global
sections of an affine étale neighbourhood. -/
theorem smallAffineEtaleCommPresheaf_obj {X : GroupoidsOver S} (x : Affine X)
    (V : (X.p.obj x.obj).left.AffineEtale) :
    (smallAffineEtaleCommPresheaf x).obj (op V) =
      CommRingCat.of
        (ULift.{u + 1, u}
          (Scheme.Γ.obj
            (op
              ((SmallStandardTopology.Affine.toOver .etale
                  (X.p.obj x.obj).left ⋙
                Over.forget (X.p.obj x.obj).left).obj V)))) :=
  sorry

/-- The unlifted comparison of global-sections presheaves induced by
`smallAffineEtaleSchemeProjection`. -/
def smallAffineEtaleCommStructurePresheafMapUnlifted {X : GroupoidsOver S}
    (x : Affine X) :
    (SmallStandardTopology.Affine.toOver .etale (X.p.obj x.obj).left ⋙
          Over.forget (X.p.obj x.obj).left).op ⋙
        Scheme.Γ ⟶
      (smallAffineEtaleToAffine x ⋙ affineInclusion X ⋙ X.p ⋙
          Over.forget S).op ⋙
        Scheme.Γ where
  app V := ((smallAffineEtaleSchemeProjection x).app V.unop).appTop
  naturality := sorry

/-- The unlifted comparison is the family of `appTop` maps of
`smallAffineEtaleSchemeProjection`. -/
theorem smallAffineEtaleCommStructurePresheafMapUnlifted_app
    {X : GroupoidsOver S} (x : Affine X)
    (V : (X.p.obj x.obj).left.AffineEtale) :
    (smallAffineEtaleCommStructurePresheafMapUnlifted x).app (op V) =
      ((smallAffineEtaleSchemeProjection x).app V).appTop :=
  sorry

/-- The comparison of structure sheaves from `𝒪_{U_affine,étale}` to the
restriction of `𝒪` along `smallAffineEtaleToAffine x`. -/
def smallAffineEtaleCommStructurePresheafMap {X : GroupoidsOver S}
    (x : Affine X) :
    smallAffineEtaleCommPresheaf x ⟶
      (smallAffineEtaleToAffine x).op ⋙ affineCommPresheaf X :=
  Functor.whiskerRight (smallAffineEtaleCommStructurePresheafMapUnlifted x)
    CommRingCat.universeLift.{u, u + 1}

/-- On an affine étale neighbourhood `V` of `U = p(x)`,
`smallAffineEtaleCommStructurePresheafMap` is the universe lift of the map on
global sections induced by the scheme projection. -/
theorem smallAffineEtaleCommStructurePresheafMap_app {X : GroupoidsOver S}
    (x : Affine X) (V : (X.p.obj x.obj).left.AffineEtale) :
    (smallAffineEtaleCommStructurePresheafMap x).app (op V) =
      (CommRingCat.universeLift.{u, u + 1}).map
        ((smallAffineEtaleSchemeProjection x).app V).appTop :=
  sorry

/-- The underlying ring-valued comparison of structure sheaves from
`𝒪_{U_affine,étale}` to the restriction of `𝒪` along
`smallAffineEtaleToAffine x`. -/
def smallAffineEtaleStructureSheafMap {X : GroupoidsOver S} (x : Affine X) :
    ringPresheaf (smallAffineEtaleCommPresheaf x) ⟶
      (smallAffineEtaleToAffine x).op ⋙ ringPresheaf (affineCommPresheaf X) :=
  Functor.whiskerRight (smallAffineEtaleCommStructurePresheafMap x)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

/-- The underlying ring map of `smallAffineEtaleStructureSheafMap` is the
forgetful image of `smallAffineEtaleCommStructurePresheafMap`. -/
theorem smallAffineEtaleStructureSheafMap_eq {X : GroupoidsOver S}
    (x : Affine X) :
    smallAffineEtaleStructureSheafMap x =
      Functor.whiskerRight (smallAffineEtaleCommStructurePresheafMap x)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  sorry

/-- The universe-lifted commutative structure presheaf on `U_affine,étale` is a
sheaf. -/
theorem smallAffineEtaleCommPresheaf_isSheaf {X : GroupoidsOver S}
    (x : Affine X) :
    Presheaf.IsSheaf (AffineEtale.topology (X.p.obj x.obj).left)
      (smallAffineEtaleCommPresheaf x) :=
  sorry

/-- The universe-lifted ring-valued structure presheaf on `U_affine,étale` is a
sheaf. -/
theorem smallAffineEtaleStructurePresheaf_isSheaf {X : GroupoidsOver S}
    (x : Affine X) :
    Presheaf.IsSheaf (AffineEtale.topology (X.p.obj x.obj).left)
      (ringPresheaf (smallAffineEtaleCommPresheaf x)) :=
  sorry

/-- The universe-lifted ring-valued structure sheaf on the small affine étale
site of `U = p(x)`. -/
def smallAffineEtaleStructureSheaf {X : GroupoidsOver S} (x : Affine X) :
    Sheaf (AffineEtale.topology (X.p.obj x.obj).left) RingCat.{u + 1} :=
  ⟨ringPresheaf (smallAffineEtaleCommPresheaf x),
    smallAffineEtaleStructurePresheaf_isSheaf x⟩

/-- The underlying presheaf of `smallAffineEtaleStructureSheaf x` is the
forgetful image of `smallAffineEtaleCommPresheaf x`. -/
theorem smallAffineEtaleStructureSheaf_obj {X : GroupoidsOver S}
    (x : Affine X) :
    (smallAffineEtaleStructureSheaf x).obj =
      ringPresheaf (smallAffineEtaleCommPresheaf x) :=
  sorry

/-- Restriction of a presheaf of `𝒪`-modules on `𝒳_affine` to the small affine
étale site of `U = p(x)`, as a presheaf of `𝒪_{U_affine,étale}`-modules. -/
def restrictToSmallAffineEtalePresheaf {X : GroupoidsOver S}
    (F : AffineModule X) (x : Affine X) :
    PresheafOfModules.{u + 1}
      (ringPresheaf (smallAffineEtaleCommPresheaf x)) :=
  (PresheafOfModules.pushforward (smallAffineEtaleStructureSheafMap x)).obj F

/-- Sections of `restrictToSmallAffineEtalePresheaf F x` over an affine étale
neighbourhood `V` are the sections of `F` on the image of `V` in `𝒳_affine`,
with scalars restricted along `smallAffineEtaleStructureSheafMap`. -/
theorem restrictToSmallAffineEtalePresheaf_obj {X : GroupoidsOver S}
    (F : AffineModule X) (x : Affine X)
    (V : (X.p.obj x.obj).left.AffineEtale) :
    (restrictToSmallAffineEtalePresheaf F x).obj (op V) =
      (ModuleCat.restrictScalars
          ((smallAffineEtaleStructureSheafMap x).app (op V)).hom).obj
        (F.obj (op ((smallAffineEtaleToAffine x).obj V))) :=
  sorry

/-- If `F` is a sheaf for the étale topology on `𝒳_affine`, then its restriction
to the small affine étale site of `U = p(x)` is a sheaf. -/
theorem restrictToSmallAffineEtalePresheaf_isSheaf {X : GroupoidsOver S}
    (F : AffineModule X) (x : Affine X)
    (hF : Presheaf.IsSheaf X.affineEtaleTopology F.presheaf) :
    Presheaf.IsSheaf (AffineEtale.topology (X.p.obj x.obj).left)
      (restrictToSmallAffineEtalePresheaf F x).presheaf :=
  sorry

/-- Restriction of a presheaf of `𝒪`-modules on `𝒳_affine` to the small affine
étale site of `U = p(x)`, packaged as a sheaf of
`𝒪_{U_affine,étale}`-modules. -/
def restrictToSmallAffineEtale {X : GroupoidsOver S} (F : AffineModule X)
    (x : Affine X) (hF : Presheaf.IsSheaf X.affineEtaleTopology F.presheaf) :
    SheafOfModules (smallAffineEtaleStructureSheaf x) where
  val := restrictToSmallAffineEtalePresheaf F x
  isSheaf := restrictToSmallAffineEtalePresheaf_isSheaf F x hF

/-- The underlying module presheaf of `restrictToSmallAffineEtale F x hF` is
`restrictToSmallAffineEtalePresheaf F x`. -/
theorem restrictToSmallAffineEtale_val {X : GroupoidsOver S}
    (F : AffineModule X) (x : Affine X)
    (hF : Presheaf.IsSheaf X.affineEtaleTopology F.presheaf) :
    (restrictToSmallAffineEtale F x hF).val =
      restrictToSmallAffineEtalePresheaf F x :=
  sorry

/-- Sections of `restrictToSmallAffineEtale F x hF` agree with
`restrictToSmallAffineEtalePresheaf` on affine étale neighbourhoods. -/
theorem restrictToSmallAffineEtale_obj {X : GroupoidsOver S}
    (F : AffineModule X) (x : Affine X)
    (hF : Presheaf.IsSheaf X.affineEtaleTopology F.presheaf)
    (V : (X.p.obj x.obj).left.AffineEtale) :
    (restrictToSmallAffineEtale F x hF).val.obj (op V) =
      (restrictToSmallAffineEtalePresheaf F x).obj (op V) :=
  sorry

/-- The sheaf condition of `restrictToSmallAffineEtale F x hF` is
`restrictToSmallAffineEtalePresheaf_isSheaf`. -/
theorem restrictToSmallAffineEtale_isSheaf {X : GroupoidsOver S}
    (F : AffineModule X) (x : Affine X)
    (hF : Presheaf.IsSheaf X.affineEtaleTopology F.presheaf) :
    (restrictToSmallAffineEtale F x hF).isSheaf =
      restrictToSmallAffineEtalePresheaf_isSheaf F x hF :=
  sorry

/-- Slice sites of the small affine étale topology support composition with the
ring-to-abelian-group forgetful functor in universe `u + 1`. -/
instance affineEtaleOver_hasSheafCompose (U : Scheme.{u})
    (V : U.AffineEtale) :
    ((AffineEtale.topology U).over V).HasSheafCompose
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) :=
  sorry

/-- Additive sheafification exists on every slice of a small affine étale site
in universe `u + 1`. -/
instance affineEtaleOver_hasWeakSheafify (U : Scheme.{u})
    (V : U.AffineEtale) :
    HasWeakSheafify ((AffineEtale.topology U).over V) AddCommGrpCat.{u + 1} :=
  sorry

/-- On every affine étale slice, sheafification equivalences in universe
`u + 1` are the locally bijective morphisms. -/
instance affineEtaleOver_wEqualsLocallyBijective (U : Scheme.{u})
    (V : U.AffineEtale) :
    ((AffineEtale.topology U).over V).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  sorry

end AlgebraicGeometry.GroupoidsOver
