/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Adjunction.LeftExact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change for localized left-exact adjunctions

This leaf owns the category-theoretic comparison between pullback in a slice and the inverse image
of a left-exact adjunction.  It is independent of sites and is therefore reusable for any geometric
morphism presented by a `LeftExactAdjunction`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe uA vA uB vB

namespace CategoryTheory.LeftExactAdjunction.Localization

variable {A : Type uA} [Category.{vA} A] [HasPullbacks A]
variable {B : Type uB} [Category.{vB} B] [HasPullbacks B]

/-- The localized inverse image followed by pullback sends a slice object to the expected
pullback object. -/
@[stacks 04IV "(object)"]
theorem inverseImagePullback_obj (f : LeftExactAdjunction A B)
    {Y : B} {X : A} (s : X ⟶ f.inverseImage.obj Y) (Z : Over Y) :
    ((f.localization Y).inverseImage ⋙ Over.pullback s).obj Z =
      Over.mk (pullback.snd (f.inverseImage.map Z.hom) s) := sorry

/-- The pullback-preservation comparison has the required compatibility with the maps to the
base of the slice. -/
theorem inverseImagePullbackIsoApp_comm (f : LeftExactAdjunction A B)
    {Y Y' : B} (b : Y' ⟶ Y) (Z : Over Y) :
    (PreservesPullback.iso f.inverseImage Z.hom b).hom ≫
        (((f.localization Y).inverseImage ⋙
          Over.pullback (f.inverseImage.map b)).obj Z).hom =
      ((Over.pullback b ⋙ (f.localization Y').inverseImage).obj Z).hom := sorry

/-- Objectwise comparison between pulling back before and after localized inverse image. -/
noncomputable def inverseImagePullbackIsoApp (f : LeftExactAdjunction A B)
    {Y Y' : B} (b : Y' ⟶ Y) (Z : Over Y) :
    (Over.pullback b ⋙ (f.localization Y').inverseImage).obj Z ≅
      ((f.localization Y).inverseImage ⋙
        Over.pullback (f.inverseImage.map b)).obj Z :=
  Over.isoMk (PreservesPullback.iso f.inverseImage Z.hom b)
    (inverseImagePullbackIsoApp_comm f b Z)

/-- The objectwise localized pullback comparisons are natural. -/
theorem inverseImagePullbackIsoApp_naturality (f : LeftExactAdjunction A B)
    {Y Y' : B} (b : Y' ⟶ Y) {Z Z' : Over Y} (g : Z ⟶ Z') :
    (Over.pullback b ⋙ (f.localization Y').inverseImage).map g ≫
        (inverseImagePullbackIsoApp f b Z').hom =
      (inverseImagePullbackIsoApp f b Z).hom ≫
        ((f.localization Y).inverseImage ⋙
          Over.pullback (f.inverseImage.map b)).map g := sorry

/-- Pullback in the target slice commutes canonically with localized inverse image. -/
@[stacks 04IV "(pullback comparison)"]
noncomputable def inverseImagePullbackIso (f : LeftExactAdjunction A B)
    {Y Y' : B} (b : Y' ⟶ Y) :
    Over.pullback b ⋙ (f.localization Y').inverseImage ≅
      (f.localization Y).inverseImage ⋙ Over.pullback (f.inverseImage.map b) :=
  NatIso.ofComponents
    (fun Z ↦ inverseImagePullbackIsoApp f b Z)
    (fun {_ _} g ↦ inverseImagePullbackIsoApp_naturality f b g)

/-- Pullback functors along the two equal composites in a localization square agree. -/
theorem pullback_eq_of_comm (f : LeftExactAdjunction A B)
    {Y Y' : B} {X X' : A} (b : Y' ⟶ Y) (a : X' ⟶ X)
    (s : X ⟶ f.inverseImage.obj Y) (s' : X' ⟶ f.inverseImage.obj Y')
    (h : s' ≫ f.inverseImage.map b = a ≫ s) :
    Over.pullback (s' ≫ f.inverseImage.map b) = Over.pullback (a ≫ s) := sorry

/-- A commutative square `s' ≫ f⁻¹(b) = a ≫ s` induces the canonical base-change
isomorphism between the corresponding localized inverse-image functors. -/
@[stacks 04IV "(base change)"]
noncomputable def inverseImageBaseChangeIso (f : LeftExactAdjunction A B)
    {Y Y' : B} {X X' : A} (b : Y' ⟶ Y) (a : X' ⟶ X)
    (s : X ⟶ f.inverseImage.obj Y) (s' : X' ⟶ f.inverseImage.obj Y')
    (h : s' ≫ f.inverseImage.map b = a ≫ s) :
    Over.pullback b ⋙ (f.localization Y').inverseImage ⋙ Over.pullback s' ≅
      (f.localization Y).inverseImage ⋙ Over.pullback s ⋙ Over.pullback a :=
  (Functor.associator (Over.pullback b) (f.localization Y').inverseImage
      (Over.pullback s')).symm ≪≫
    Functor.isoWhiskerRight (inverseImagePullbackIso f b) (Over.pullback s') ≪≫
    Functor.associator (f.localization Y).inverseImage
      (Over.pullback (f.inverseImage.map b)) (Over.pullback s') ≪≫
    Functor.isoWhiskerLeft (f.localization Y).inverseImage
      ((Over.pullbackComp s' (f.inverseImage.map b)).symm ≪≫
        eqToIso (pullback_eq_of_comm f b a s s' h) ≪≫ Over.pullbackComp a s) ≪≫
    Functor.associator (f.localization Y).inverseImage (Over.pullback s) (Over.pullback a)

end CategoryTheory.LeftExactAdjunction.Localization
