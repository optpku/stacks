module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Postcomposition
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Precomposition
public import stacks_project.Chap78.Lemma_78_22_2_Square
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.AtlasNaturality

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

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.atlasToPreQuotient_comp_prestackMap :
  ∀ (f : Hom G H),
    (atlasToPreQuotient G).comp (prestackMap f) =
      (stackInSets.map f.obj.left).comp (atlasToPreQuotient H))

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.atlasIsoCore :
  ∀ (f : Hom G H),
    (fppfAtlas G).comp (quotientStackMap f) ≅
      (stackInSets.map f.obj.left).comp (fppfAtlas H))

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.atlasIsoULift :
  ∀ (f : Hom G H),
    (fppfAtlasULift G).comp (quotientStackMap f) ≅
      ((stackInSetsULift.down G.U.left).comp
          ((stackInSets.map f.obj.left).comp (stackInSetsULift.up H.U.left))).comp
        (fppfAtlasULift H))

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.atlasConeIso :
  ∀ (f : Hom G H),
    atlasULiftHom G ≫ isoCommaConeRight f ≅
      stackInSetsULift.map f.obj.left ≫ isoCommaConeBottom f)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.atlasCone :
  ∀ (f : Hom G H),
    PseudoPullbackCone (isoCommaConeRight f) (isoCommaConeBottom f))

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.atlasCone_pt :
  ∀ (f : Hom G H),
    (atlasCone f).pt = stackInSetsULift G.U.left)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.atlasCone_fst :
  ∀ (f : Hom G H),
    (atlasCone f).fst = atlasULiftHom G)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.atlasCone_snd :
  ∀ (f : Hom G H),
    (atlasCone f).snd = stackInSetsULift.map f.obj.left)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.atlasCone_iso :
  ∀ (f : Hom G H),
    (atlasCone f).iso = atlasConeIso f)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.isPullback_source_iff_target :
  ∀ (f : Hom G H),
    IsPullback f.arrow G.s H.s f.obj ↔ IsPullback f.arrow G.t H.t f.obj)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.isPullback_source_iff_left :
  ∀ (f : Hom G H),
    IsPullback f.arrow G.s H.s f.obj ↔
      IsPullback f.arrow.left G.s.left H.s.left f.obj.left)

end AlgebraicGeometry.GroupoidAlgebraicSpace.Hom
