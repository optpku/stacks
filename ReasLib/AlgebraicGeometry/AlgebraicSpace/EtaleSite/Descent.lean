/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationInclusion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SheafPseudofunctor

/-!
# Descent of small étale sheaves along an étale covering

An étale covering of algebraic spaces determines descent data for sheaves on the
spaces-étale site. The canonical functor from small étale sheaves is an equivalence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type u}
  {Xᵢ : ι → AlgebraicSpace S}

/-- The object of `X_spaces,étale` given by an étale morphism `f i : Xᵢ i ⟶ X`. -/
def etaleCoveringObj (f : ∀ i, Xᵢ i ⟶ X) [∀ i, Etale (f i)] (i : ι) :
    spacesEtaleSite X :=
  MorphismProperty.Over.mk ⊤ (f i) inferInstance

/-- The underlying algebraic space of `etaleCoveringObj f i` is `Xᵢ i`. -/
theorem etaleCoveringObj_left (f : ∀ i, Xᵢ i ⟶ X) [∀ i, Etale (f i)] (i : ι) :
    (etaleCoveringObj f i).left = Xᵢ i :=
  rfl

/-- The structural morphism of `etaleCoveringObj f i` is `f i`. -/
theorem etaleCoveringObj_hom (f : ∀ i, Xᵢ i ⟶ X) [∀ i, Etale (f i)] (i : ι) :
    (etaleCoveringObj f i).hom = f i :=
  rfl

/-- The structure morphism of `etaleCoveringObj f i` toward the terminal object of
`X_spaces,étale`. -/
def etaleCoveringToSelf (f : ∀ i, Xᵢ i ⟶ X) [∀ i, Etale (f i)] (i : ι) :
    etaleCoveringObj f i ⟶ spacesEtaleSite.self X :=
  spacesEtaleSite.homToSelf (etaleCoveringObj f i)

/-- The underlying morphism of `etaleCoveringToSelf f i` is `f i`. -/
theorem etaleCoveringToSelf_left (f : ∀ i, Xᵢ i ⟶ X) [∀ i, Etale (f i)] (i : ι) :
    (etaleCoveringToSelf f i).left = f i :=
  rfl

/-- Descent data for étale sheaves of types along the covering `{f i : Xᵢ i ⟶ X}`
in `X_spaces,étale`. -/
abbrev etaleCoveringDescent (f : ∀ i, Xᵢ i ⟶ X) [∀ i, Etale (f i)] :=
  ((spacesEtaleTopology X).pseudofunctorOver (Type (u + 1))).DescentData
    (fun i ↦ etaleCoveringToSelf f i)

/-- The functor sending a small étale sheaf on `X` to its descent datum along an
étale covering `{f i : Xᵢ i ⟶ X}`. -/
def sheafToEtaleCoveringDescent (f : ∀ i, Xᵢ i ⟶ X) [∀ i, Etale (f i)] :
    Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤ etaleCoveringDescent f :=
  smallEtalePresentationExtension X ⋙
    (spacesEtaleTopology X).overPullback (Type (u + 1)) (spacesEtaleSite.self X) ⋙
      ((spacesEtaleTopology X).pseudofunctorOver (Type (u + 1))).toDescentData
        (fun i ↦ etaleCoveringToSelf f i)

/-- The object map of `sheafToEtaleCoveringDescent f` is restriction to the slice
over the terminal object, followed by `toDescentData` of the covering. -/
theorem sheafToEtaleCoveringDescent_obj (f : ∀ i, Xᵢ i ⟶ X) [∀ i, Etale (f i)]
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (sheafToEtaleCoveringDescent f).obj F =
      (((spacesEtaleTopology X).pseudofunctorOver (Type (u + 1))).toDescentData
          (fun i ↦ etaleCoveringToSelf f i)).obj
        (((spacesEtaleTopology X).overPullback (Type (u + 1))
            (spacesEtaleSite.self X)).obj
          ((smallEtalePresentationExtension X).obj F)) :=
  rfl

/-- The canonical functor from small étale sheaves to descent data along a jointly
surjective family of étale morphisms is an equivalence of categories. -/
theorem sheafToEtaleCoveringDescent_isEquivalence
    (f : ∀ i, Xᵢ i ⟶ X) [∀ i, Etale (f i)]
    (h_cover : (⋃ i, Set.range (Points.map (f i))) = Set.univ) :
    (sheafToEtaleCoveringDescent f).IsEquivalence :=
  sorry

/-- The canonical descent functor is an equivalence when joint surjectivity of the
étale family is available as a fact. -/
instance instSheafToEtaleCoveringDescentIsEquivalence
    (f : ∀ i, Xᵢ i ⟶ X) [∀ i, Etale (f i)]
    [h_cover : Fact ((⋃ i, Set.range (Points.map (f i))) = Set.univ)] :
    (sheafToEtaleCoveringDescent f).IsEquivalence :=
  sheafToEtaleCoveringDescent_isEquivalence f h_cover.out

namespace EtaleSheaf

/-- Descent of small étale sheaves along a morphism of algebraic spaces is an
equivalence if it is an equivalence after base change to each member of a jointly
surjective étale family and to each pairwise overlap of that family. -/
theorem descentIsEquivalenceOfBaseChangeOfEtaleCovering
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {ι : Type u} {Yᵢ : ι → AlgebraicSpace S} (g : ∀ i, Yᵢ i ⟶ Y) [∀ i, Etale (g i)]
    (h_cover : (⋃ i, Set.range (Points.map (g i))) = Set.univ)
    (h_i : ∀ i, (pseudofunctor.toDescentData
      (fun _ : PUnit ↦ Limits.pullback.snd f (g i))).IsEquivalence)
    (h_ij : ∀ i j, (pseudofunctor.toDescentData
      (fun _ : PUnit ↦ Limits.pullback.snd f
        (Limits.pullback.fst (g i) (g j) ≫ g i))).IsEquivalence) :
    (pseudofunctor.toDescentData (fun _ : PUnit ↦ f)).IsEquivalence :=
  sorry


end EtaleSheaf

end AlgebraicGeometry.AlgebraicSpace
