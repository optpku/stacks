/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic

/-!
# Small affine Zariski site carrier

This leaf owns the full category of affine opens of a scheme with arbitrary
inclusions, together with its comparison topology induced from the category of
all opens.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

/-- The object property on `S.Opens` selecting affine open subschemes. -/
abbrev affineOpenObjects : ObjectProperty S.Opens :=
  fun U ↦ IsAffineOpen U

/-- Affine opens of a scheme are closed under isomorphisms in its category of
opens. -/
theorem affineOpenObjects_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (affineOpenObjects S) := sorry

/-- Typeclass access to isomorphism closure of affine opens. -/
instance affineOpenObjectsIsClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (affineOpenObjects S) :=
  affineOpenObjects_isClosedUnderIsomorphisms S

/-- Affine opens of a scheme are closed under pullbacks in its category of
opens. -/
theorem affineOpenObjects_isClosedUnderLimitsOfShape_walkingCospan :
    ObjectProperty.IsClosedUnderLimitsOfShape (affineOpenObjects S) WalkingCospan := sorry

/-- Typeclass access to pullback closure of affine opens. -/
instance affineOpenObjectsIsClosedUnderLimitsOfShapeWalkingCospan :
    ObjectProperty.IsClosedUnderLimitsOfShape (affineOpenObjects S) WalkingCospan :=
  affineOpenObjects_isClosedUnderLimitsOfShape_walkingCospan S

/-- The small affine Zariski site of `S` is the full subcategory of affine open
subschemes of `S`, with all inclusions between them. -/
@[stacks 020T]
abbrev smallAffineZariskiSite : Type u :=
  ObjectProperty.FullSubcategory (affineOpenObjects S)

/-- Every object of the small affine Zariski site is an affine open of `S`. -/
theorem smallAffineZariskiSite_obj_isAffineOpen (U : S.smallAffineZariskiSite) :
    IsAffineOpen U.obj := sorry

/-- The inclusion of affine opens into the category of all opens of `S`. -/
abbrev smallAffineZariskiToOpens : S.smallAffineZariskiSite ⥤ S.Opens :=
  ObjectProperty.ι (affineOpenObjects S)

/-- The affine-open inclusion sends an object to its underlying open subset. -/
@[simp] theorem smallAffineZariskiToOpens_obj (U : S.smallAffineZariskiSite) :
    (smallAffineZariskiToOpens S).obj U = U.obj := sorry

/-- The affine-open inclusion forgets only the affine-open property of a
morphism. -/
@[simp] theorem smallAffineZariskiToOpens_map
    {U V : S.smallAffineZariskiSite} (f : U ⟶ V) :
    (smallAffineZariskiToOpens S).map f = f.hom := sorry

/-- The inclusion of the small affine Zariski site into the small Zariski
site of `S`. -/
abbrev smallAffineZariskiInclusion : S.smallAffineZariskiSite ⥤ S.smallZariskiSite :=
  smallAffineZariskiToOpens S ⋙ smallZariskiOpenFunctor S

/-- The source-scheme functor from the small affine Zariski site. -/
abbrev smallAffineZariskiToScheme : S.smallAffineZariskiSite ⥤ Scheme :=
  smallAffineZariskiInclusion S ⋙ smallZariskiToScheme S

/-- The small affine inclusion sends an affine open to the corresponding open
immersion over `S`. -/
@[simp] theorem smallAffineZariskiInclusion_obj_hom (U : S.smallAffineZariskiSite) :
    ((smallAffineZariskiInclusion S).obj U).hom = U.obj.ι := sorry

/-- The source scheme of a small affine Zariski object is its underlying open
subscheme. -/
@[simp] theorem smallAffineZariskiInclusion_obj_left (U : S.smallAffineZariskiSite) :
    ((smallAffineZariskiInclusion S).obj U).left = U.obj := sorry

/-- The small affine inclusion takes an inclusion of affine opens to the
corresponding morphism of open subschemes. -/
@[simp] theorem smallAffineZariskiInclusion_map_left
    {U V : S.smallAffineZariskiSite} (f : U ⟶ V) :
    ((smallAffineZariskiInclusion S).map f).left = S.homOfLE f.hom.le := sorry

/-- The source-scheme functor sends an affine open to its associated open
subscheme. -/
@[simp] theorem smallAffineZariskiToScheme_obj (U : S.smallAffineZariskiSite) :
    (smallAffineZariskiToScheme S).obj U = U.obj := sorry

/-- The source-scheme functor takes an inclusion of affine opens to the
corresponding morphism of open subschemes. -/
@[simp] theorem smallAffineZariskiToScheme_map
    {U V : S.smallAffineZariskiSite} (f : U ⟶ V) :
    (smallAffineZariskiToScheme S).map f = S.homOfLE f.hom.le := sorry

/-- Forgetting the open-immersion condition after the small affine inclusion
is the ordinary restriction functor on affine opens. -/
theorem smallAffineZariskiInclusion_comp_forget :
    smallAffineZariskiInclusion S ⋙ smallZariskiForget S =
      smallAffineZariskiToOpens S ⋙ S.restrictFunctor := sorry

/-- The source-scheme functor factors through the restriction functor on
affine opens. -/
theorem smallAffineZariskiToScheme_eq :
    smallAffineZariskiToScheme S =
      smallAffineZariskiToOpens S ⋙ S.restrictFunctor ⋙ Over.forget S := sorry

/-- The small affine Zariski site has pullbacks. -/
instance smallAffineZariskiSite_hasPullbacks : HasPullbacks S.smallAffineZariskiSite :=
  inferInstance

/-- The source-scheme functor from the small affine Zariski site preserves
pullbacks. -/
theorem smallAffineZariskiToScheme_preservesPullbacks_spec :
    PreservesLimitsOfShape WalkingCospan (smallAffineZariskiToScheme S) := sorry

/-- Typeclass access to pullback preservation by the small affine source
functor. -/
instance smallAffineZariskiToScheme_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (smallAffineZariskiToScheme S) :=
  smallAffineZariskiToScheme_preservesPullbacks_spec S

/-- The ambient topology of opens restricted to affine opens of `S`. This is
a comparison topology, distinct from the standard-cover topology in
`ZariskiSite.Affine.Cover`. -/
abbrev smallAffineZariskiRestrictedPrecoverage : Precoverage S.smallAffineZariskiSite :=
  (Opens.grothendieckTopology S).toPrecoverage.comap (smallAffineZariskiToOpens S)

/-- A presieve is covering for the ambient restricted topology on affine
opens exactly when its image is covering in `S.Opens`. -/
@[simp] theorem mem_smallAffineZariskiRestrictedPrecoverage_iff
    {U : S.smallAffineZariskiSite} {R : Presieve U} :
    R ∈ smallAffineZariskiRestrictedPrecoverage S U ↔
      R.map (smallAffineZariskiToOpens S) ∈
        (Opens.grothendieckTopology S).toPrecoverage U.obj := sorry

/-- The Grothendieck topology on affine opens obtained by restricting the
ambient topology on `S.Opens`. -/
abbrev smallAffineZariskiRestrictedTopology : GrothendieckTopology S.smallAffineZariskiSite :=
  (smallAffineZariskiRestrictedPrecoverage S).toGrothendieck

/-- The ambient restricted small affine Zariski topology is generated by its
restricted precoverage. -/
theorem smallAffineZariskiRestrictedTopology_def :
    smallAffineZariskiRestrictedTopology S =
      (smallAffineZariskiRestrictedPrecoverage S).toGrothendieck := sorry

end AlgebraicGeometry.Scheme
