/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Hom
public import ReasLib.CategoryTheory.Sites.Topos.Point.TypeImage
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Site points recovered from topos points

This module constructs the site point represented by the inverse image of a
topos point on sheafified representables.  The point's fiber is explicit;
the cofilteredness, smallness, and covering conditions are separate theorem
interfaces so downstream users can reuse the construction independently of
their eventual proofs.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite Functor

universe u v

noncomputable section

namespace CategoryTheory.MorphismOfTopoiIn

open scoped GrothendieckTopology.SheafifiedRepresentable

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/-- The fiber functor on a site obtained by evaluating a topos point on sheafified
representables. -/
abbrev sitePointFiber
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    C ⥤ Type (max u v) :=
  J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage

/-- The category of elements of the fiber represented by a topos point is cofiltered. -/
theorem sitePointFiber_isCofiltered
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    IsCofiltered (sitePointFiber (J := J) p).Elements := sorry

/-- The category of elements of the fiber represented by a topos point is initially small. -/
theorem sitePointFiber_initiallySmall
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    InitiallySmall.{max u v} (sitePointFiber (J := J) p).Elements := sorry

/-- Covering sieves act jointly surjectively on the fiber represented by a topos point. -/
theorem sitePointFiber_jointlySurjective
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    ∀ {U : C} (R : Sieve U) (hR : R ∈ J U) (x : (sitePointFiber (J := J) p).obj U),
      ∃ (Y : C) (f : Y ⟶ U) (_ : R f) (y : (sitePointFiber (J := J) p).obj Y),
        (sitePointFiber (J := J) p).map f y = x := sorry

/-- The site point canonically associated to a point of the topos `Sh(C, J)`. -/
@[stacks 00YA "(1)"]
noncomputable def toSitePoint
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    GrothendieckTopology.Point.{max u v} J where
  fiber := sitePointFiber (J := J) p
  isCofiltered := sitePointFiber_isCofiltered (J := J) p
  initiallySmall := sitePointFiber_initiallySmall (J := J) p
  jointly_surjective := sitePointFiber_jointlySurjective (J := J) p

namespace ToSitePoint

/-- Sections of the direct image of a topos point over a sheafified representable are functions
on the corresponding fiber of its associated site point. -/
noncomputable def sectionEquiv
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    (E : Type (max u v)) (U : C) :
    (p.typePushforward.obj E).obj.obj (op U) ≃ (p.toSitePoint.fiber.obj U → E) :=
  (J.sheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm.trans
    ((p.typeAdjunction.homEquiv (h[U]^#[J]) E).symm.trans TypeCat.homEquiv)

/-- The section equivalence at one object, expressed as an isomorphism of `Type` objects. -/
noncomputable def sectionObjIso
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    (E : Type (max u v)) (U : Cᵒᵖ) :
    (p.typePushforward.obj E).obj.obj U ≅ (p.toSitePoint.skyscraperPresheaf E).obj U :=
  (Equiv.toIso (sectionEquiv (J := J) p E U.unop)) ≪≫
    (Types.productIso (fun _ : p.toSitePoint.fiber.obj U.unop ↦ E)).symm

/-- The objectwise section comparison is natural in restriction maps of the site. -/
theorem sectionObjIso_naturality
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    (E : Type (max u v)) {U V : Cᵒᵖ} (f : U ⟶ V) :
    (p.typePushforward.obj E).obj.map f ≫ (sectionObjIso (J := J) p E V).hom =
      (sectionObjIso (J := J) p E U).hom ≫ (p.toSitePoint.skyscraperPresheaf E).map f := sorry

/-- The direct image of one type object agrees with the skyscraper presheaf of the associated
site point. -/
noncomputable def presheafObjIso
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    (E : Type (max u v)) :
    (p.typePushforward.obj E).obj ≅ p.toSitePoint.skyscraperPresheaf E :=
  NatIso.ofComponents (sectionObjIso (J := J) p E)
    (fun f ↦ sectionObjIso_naturality (J := J) p E f)

/-- The presheaf comparison is natural in the type object sent through the direct image. -/
theorem presheafObjIso_naturality
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    {E E' : Type (max u v)} (f : E ⟶ E') :
    (p.typePushforward ⋙ sheafToPresheaf J (Type (max u v))).map f ≫
        (presheafObjIso (J := J) p E').hom =
      (presheafObjIso (J := J) p E).hom ≫
        p.toSitePoint.skyscraperPresheafFunctor.map f := sorry

/-- The direct image of a topos point agrees, after forgetting to presheaves, with the
skyscraper presheaf functor of its associated site point. -/
noncomputable def typePushforwardPresheafIso
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    p.typePushforward ⋙ sheafToPresheaf J (Type (max u v)) ≅
      p.toSitePoint.skyscraperPresheafFunctor :=
  NatIso.ofComponents (presheafObjIso (J := J) p)
    (fun f ↦ presheafObjIso_naturality (J := J) p f)

/-- The direct image of a topos point is the skyscraper sheaf functor of its associated
site point. -/
noncomputable def typePushforwardIso
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    p.typePushforward ≅ p.toSitePoint.skyscraperSheafFunctor :=
  Functor.fullyFaithfulCancelRight (sheafToPresheaf J (Type (max u v)))
    (typePushforwardPresheafIso (J := J) p)

/-- Lemma 7.32.7: the sheaf fiber of the site point associated to a topos point is the inverse
image of the original topos point. -/
@[stacks 00YA "(2)"]
noncomputable def sheafFiberIso
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    p.toSitePoint.sheafFiber ≅ p.typeInverseImage :=
  Adjunction.leftAdjointUniq p.toSitePoint.skyscraperSheafAdjunction
    (p.typeAdjunction.ofNatIsoRight (typePushforwardIso (J := J) p))

end ToSitePoint

end CategoryTheory.MorphismOfTopoiIn
