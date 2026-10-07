module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Postcomposition
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Precomposition
public import stacks_project.Chap78.Lemma_78_22_2_Square

/-!
# Atlas square of a morphism of groupoids in algebraic spaces

A morphism `f : Hom G H` determines cartesian functors `π : 𝒮_U ⟶ [U/R]`,
`𝒮(f.obj) : 𝒮_U ⟶ 𝒮_{U'}`, `[f] : [U/R] ⟶ [U'/R']`, and `π' : 𝒮_{U'} ⟶ [U'/R']`
over `(Sch/S)_fppf`. After aligning Hom-universes, these form a cone on the same
cospan `([f], π')` as `isoCommaCone`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace CategoryTheory.Limits Opposite
open CategoryTheory.Bicategory CategoryTheory.Functor
open Functor.IsFibered.InGroupoids.Stackification
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.Hom

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}

/-- Identity-on-objects associator identifying `((down ≫ atlas_G) ≫ [f])` with
`down ≫ (atlas_G ≫ [f])`. -/
def atlasIsoLeftAssoc (f : Hom G H) :
    (fppfAtlasULift G).comp (quotientStackMap f) ≅
      (stackInSetsULift.down G.U.left).comp
        ((fppfAtlas G).comp (quotientStackMap f)) where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun (x : (stackInSetsULift G.U.left).total) ↦
          𝟙 (((fppfAtlasULift G).comp (quotientStackMap f)).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun (x : (stackInSetsULift G.U.left).total) ↦
          𝟙 (((fppfAtlasULift G).comp (quotientStackMap f)).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Identity-on-objects associator identifying `((atlasToPreQuotient ≫ i_G) ≫ [f])` with
`atlasToPreQuotient ≫ (i_G ≫ [f])`. -/
def atlasIsoInnerAssoc (f : Hom G H) :
    (fppfAtlas G).comp (quotientStackMap f) ≅
      (atlasToPreQuotient G).comp
        ((fppfQuotientStackPresentation G).comparison.comp (quotientStackMap f)) where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun (x : (stackInSets G.U.left).total) ↦
          𝟙 (((fppfAtlas G).comp (quotientStackMap f)).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun (x : (stackInSets G.U.left).total) ↦
          𝟙 (((fppfAtlas G).comp (quotientStackMap f)).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Identity-on-objects associator identifying `atlasToPreQuotient ≫ prestackToQuotient` with
`(atlasToPreQuotient ≫ prestackMap) ≫ i_H`. -/
def atlasIsoPreAssoc (f : Hom G H) :
    (atlasToPreQuotient G).comp (prestackToQuotient f) ≅
      ((atlasToPreQuotient G).comp (prestackMap f)).comp
        (fppfQuotientStackPresentation H).comparison where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun (x : (stackInSets G.U.left).total) ↦
          𝟙 (((atlasToPreQuotient G).comp (prestackToQuotient f)).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun (x : (stackInSets G.U.left).total) ↦
          𝟙 (((atlasToPreQuotient G).comp (prestackToQuotient f)).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Before stackification, the atlas of `G` followed by `[f]_p` is the map of stacks in sets
induced by `f.obj` followed by the atlas of `H`. -/
theorem atlasToPreQuotient_comp_prestackMap (f : Hom G H) :
    (atlasToPreQuotient G).comp (prestackMap f) =
      (stackInSets.map f.obj.left).comp (atlasToPreQuotient H) := sorry

/-- The prestack `2`-isomorphism `atlas_G,p ≫ [f]_p ≅ 𝒮(f.obj) ≫ atlas_H,p`. -/
def atlasPreIso (f : Hom G H) :
    (atlasToPreQuotient G).comp (prestackMap f) ≅
      (stackInSets.map f.obj.left).comp (atlasToPreQuotient H) :=
  eqToIso (atlasToPreQuotient_comp_prestackMap f)

/-- Identity-on-objects associator identifying `(𝒮(f.obj) ≫ atlasToPreQuotient_H) ≫ i_H` with
`𝒮(f.obj) ≫ atlas_H`. -/
def atlasIsoRightAssoc (f : Hom G H) :
    ((stackInSets.map f.obj.left).comp (atlasToPreQuotient H)).comp
        (fppfQuotientStackPresentation H).comparison ≅
      (stackInSets.map f.obj.left).comp (fppfAtlas H) where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun (x : (stackInSets G.U.left).total) ↦
          𝟙 (((stackInSets.map f.obj.left).comp (fppfAtlas H)).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun (x : (stackInSets G.U.left).total) ↦
          𝟙 (((stackInSets.map f.obj.left).comp (fppfAtlas H)).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The unlifted atlas naturality `2`-isomorphism `atlas_G ≫ [f] ≅ 𝒮(f.obj) ≫ atlas_H`. -/
def atlasIsoCore (f : Hom G H) :
    (fppfAtlas G).comp (quotientStackMap f) ≅
      (stackInSets.map f.obj.left).comp (fppfAtlas H) :=
  atlasIsoInnerAssoc f ≪≫
    (CartesianBasedFunctor.precomp (fppfQuotientStack H).p
        (atlasToPreQuotient G)).mapIso (quotientStackMap_comp f) ≪≫
    atlasIsoPreAssoc f ≪≫
    (CartesianBasedFunctor.postcomp (stackInSets G.U.left).p
        (fppfQuotientStackPresentation H).comparison).mapIso (atlasPreIso f) ≪≫
    atlasIsoRightAssoc f

/-- Comparison identifying `𝒮(f.obj) ≫ atlas_H` with the universe-aligned composite into
`𝒮_{U'}`, using the unit of the two-universe equivalence of `𝒮_{U'}`. -/
def atlasAlignedAssoc (f : Hom G H) :
    (stackInSets.map f.obj.left).comp (fppfAtlas H) ≅
      ((stackInSets.map f.obj.left).comp (stackInSetsULift.up H.U.left)).comp
        (fppfAtlasULift H) where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun (x : (stackInSets G.U.left).total) ↦
          (fppfAtlas H).toFunctor.map
            ((Cat.TwoULift.equiv.{u + 1, u, u + 1, u + 1}
                (stackInSets H.U.left).total).unitIso.hom.app
              ((stackInSets.map f.obj.left).toFunctor.obj x))
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun (x : (stackInSets G.U.left).total) ↦
          (fppfAtlas H).toFunctor.map
            ((Cat.TwoULift.equiv.{u + 1, u, u + 1, u + 1}
                (stackInSets H.U.left).total).unitIso.inv.app
              ((stackInSets.map f.obj.left).toFunctor.obj x))
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Identity-on-objects associator identifying `down ≫ ((𝒮(f.obj) ≫ up) ≫ atlas_H)` with
`(down ≫ (𝒮(f.obj) ≫ up)) ≫ atlas_H`. -/
def atlasIsoULiftRightAssoc (f : Hom G H) :
    (stackInSetsULift.down G.U.left).comp
        (((stackInSets.map f.obj.left).comp (stackInSetsULift.up H.U.left)).comp
          (fppfAtlasULift H)) ≅
      ((stackInSetsULift.down G.U.left).comp
          ((stackInSets.map f.obj.left).comp (stackInSetsULift.up H.U.left))).comp
        (fppfAtlasULift H) where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun (x : (stackInSetsULift G.U.left).total) ↦
          𝟙 (((stackInSetsULift.down G.U.left).comp
              (((stackInSets.map f.obj.left).comp (stackInSetsULift.up H.U.left)).comp
                (fppfAtlasULift H))).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun (x : (stackInSetsULift G.U.left).total) ↦
          𝟙 (((stackInSetsULift.down G.U.left).comp
              (((stackInSets.map f.obj.left).comp (stackInSetsULift.up H.U.left)).comp
                (fppfAtlasULift H))).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The cartesian-level naturality `2`-isomorphism
`atlas_G ≫ [f] ≅ 𝒮(f.obj) ≫ atlas_H` after aligning Hom-universes. -/
def atlasIsoULift (f : Hom G H) :
    (fppfAtlasULift G).comp (quotientStackMap f) ≅
      ((stackInSetsULift.down G.U.left).comp
          ((stackInSets.map f.obj.left).comp (stackInSetsULift.up H.U.left))).comp
        (fppfAtlasULift H) :=
  atlasIsoLeftAssoc f ≪≫
    (CartesianBasedFunctor.precomp (fppfQuotientStack H).p
        (stackInSetsULift.down G.U.left)).mapIso (atlasIsoCore f ≪≫ atlasAlignedAssoc f) ≪≫
    atlasIsoULiftRightAssoc f

/-- The packaged `2`-isomorphism `π ≫ [f] ≅ 𝒮(f.obj) ≫ π'` of the atlas square. -/
def atlasConeIso (f : Hom G H) :
    atlasULiftHom G ≫ isoCommaConeRight f ≅
      stackInSetsULift.map f.obj.left ≫ isoCommaConeBottom f :=
  StackOver.Groupoids.Hom.isoMk
    (FiberedCategoryOver.Groupoids.BasedFunctorIso.lift
      (CartesianBasedFunctor.toBasedIso (atlasIsoULift f)))

/-- The `2`-commutative square with apex `𝒮_U`, first leg the atlas of `G`, second leg
`𝒮(f.obj)`, and cospan `([f], atlas of H)`. -/
def atlasCone (f : Hom G H) :
    PseudoPullbackCone (isoCommaConeRight f) (isoCommaConeBottom f) where
  pt := stackInSetsULift G.U.left
  fst := atlasULiftHom G
  snd := stackInSetsULift.map f.obj.left
  iso := atlasConeIso f

/-- The apex of `atlasCone f` is `𝒮_U`. -/
theorem atlasCone_pt (f : Hom G H) :
    (atlasCone f).pt = stackInSetsULift G.U.left := sorry

/-- The first projection of `atlasCone f` is the atlas `π : 𝒮_U ⟶ [U/R]`. -/
theorem atlasCone_fst (f : Hom G H) :
    (atlasCone f).fst = atlasULiftHom G := sorry

/-- The second projection of `atlasCone f` is `𝒮(f.obj) : 𝒮_U ⟶ 𝒮_{U'}`. -/
theorem atlasCone_snd (f : Hom G H) :
    (atlasCone f).snd = stackInSetsULift.map f.obj.left := sorry

/-- The `2`-cell of `atlasCone f` is `atlasConeIso f`. -/
theorem atlasCone_iso (f : Hom G H) :
    (atlasCone f).iso = atlasConeIso f := sorry

/-- The source square of `f` is cartesian if and only if the target square is cartesian. -/
theorem isPullback_source_iff_target (f : Hom G H) :
    IsPullback f.arrow G.s H.s f.obj ↔ IsPullback f.arrow G.t H.t f.obj := sorry

/-- Cartesianness of the source square of `f` in `Over B` is equivalent to cartesianness of the
underlying square of algebraic spaces. -/
theorem isPullback_source_iff_left (f : Hom G H) :
    IsPullback f.arrow G.s H.s f.obj ↔
      IsPullback f.arrow.left G.s.left H.s.left f.obj.left := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.Hom

