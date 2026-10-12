/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.HomologyFunctor

/-!
# Abutment functors for Cartan--Eilenberg resolutions

Mapped-total cohomology, both filtered-total cohomologies, and bounded-below right-derived
cohomology are functors on bundled Cartan--Eilenberg resolutions.  The pointwise abutment
comparisons assemble into natural isomorphisms between these functors.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CochainComplex.CartanEilenbergResolution.Bundled

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (F : A ⥤ B) [F.Additive] [HasDerivedCategory.{w} B]
variable {E : Type u₃} [Category.{v₃} E]
variable (Q : HomotopyCategory.Plus A ⥤ E)
variable [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
variable [Functor.RightDerived.EverywhereDefined F.toBoundedBelowDerived
  (HomotopyCategory.Plus.quasiIso A)]

/-- Naturality of the mapped-total comparison, stated on the bundled resolution category. -/
@[reassoc, stacks 015J "naturality of the mapped-total abutment comparison"]
theorem mappedTotalHomologyIso_naturality (n : ℤ) {X Y : Bundled A} (f : X ⟶ Y) :
    (mappedTotalHomology F n).map f ≫
        (MappedTotal.homologyIso Y.resolution F Q n).hom =
      (MappedTotal.homologyIso X.resolution F Q n).hom ≫
        (derivedHomology F Q n).map f := sorry

/-- The mapped-total cohomology comparison as a natural isomorphism. -/
@[stacks 015J "mapped-total abutment comparison of Cartan-Eilenberg resolutions"]
noncomputable def mappedTotalHomologyIso (n : ℤ) :
    mappedTotalHomology F n ≅ derivedHomology F Q n :=
  NatIso.ofComponents
    (fun X => MappedTotal.homologyIso X.resolution F Q n)
    (mappedTotalHomologyIso_naturality F Q n)

/-- The forward component of the mapped-total comparison is the pointwise abutment map. -/
@[simp, stacks 015J "mapped-total abutment comparison of Cartan-Eilenberg resolutions"]
theorem mappedTotalHomologyIso_hom_app (n : ℤ) (X : Bundled A) :
    (mappedTotalHomologyIso F Q n).hom.app X =
      (MappedTotal.homologyIso X.resolution F Q n).hom := sorry

/-- The inverse component of the mapped-total comparison is the inverse pointwise
abutment map. -/
@[simp, stacks 015J "mapped-total abutment comparison of Cartan-Eilenberg resolutions"]
theorem mappedTotalHomologyIso_inv_app (n : ℤ) (X : Bundled A) :
    (mappedTotalHomologyIso F Q n).inv.app X =
      (MappedTotal.homologyIso X.resolution F Q n).inv := sorry

/-- Inverse naturality of the mapped-total abutment comparison. -/
@[reassoc, stacks 015J "inverse naturality of the mapped-total abutment comparison"]
theorem mappedTotalHomologyIso_inv_naturality (n : ℤ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (derivedHomology F Q n).map f ≫ (mappedTotalHomologyIso F Q n).inv.app Y =
      (mappedTotalHomologyIso F Q n).inv.app X ≫ (mappedTotalHomology F n).map f := sorry

/-- Conjugating a mapped-total cohomology map by the abutment comparison recovers the source map.
-/
@[reassoc, stacks 015J "source-map computation for the mapped-total abutment comparison"]
theorem mappedTotalHomologyIso_source_map (n : ℤ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (mappedTotalHomologyIso F Q n).hom.app X ≫
        (derivedHomology F Q n).map f ≫
      (mappedTotalHomologyIso F Q n).inv.app Y =
      (mappedTotalHomology F n).map f := sorry

/-- Conjugating a mapped-total map by the inverse abutment comparison recovers the target map. -/
@[reassoc, stacks 015J "target-map computation for the mapped-total abutment comparison"]
theorem mappedTotalHomologyIso_target_map (n : ℤ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (mappedTotalHomologyIso F Q n).inv.app X ≫
        (mappedTotalHomology F n).map f ≫
      (mappedTotalHomologyIso F Q n).hom.app Y =
      (derivedHomology F Q n).map f := sorry

namespace First

/-- Naturality of the first-filtered abutment comparison on bundled resolutions. -/
@[reassoc, stacks 015J "naturality of the first-filtered abutment comparison"]
theorem filteredTotalHomologyIso_naturality (n : ℤ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (filteredTotalHomology F n).map f ≫
        (CartanEilenbergResolution.First.filteredTotalHomologyIso
          Y.resolution F Q n).hom =
      (CartanEilenbergResolution.First.filteredTotalHomologyIso
        X.resolution F Q n).hom ≫ (derivedHomology F Q n).map f := sorry

/-- The first-filtered abutment comparison as a natural isomorphism. -/
@[stacks 015J "first-filtered abutment comparison of Cartan-Eilenberg resolutions"]
noncomputable def filteredTotalHomologyIso (n : ℤ) :
    filteredTotalHomology F n ≅ derivedHomology F Q n :=
  NatIso.ofComponents
    (fun X => CartanEilenbergResolution.First.filteredTotalHomologyIso
      X.resolution F Q n)
    (filteredTotalHomologyIso_naturality F Q n)

/-- The forward component of the first-filtered comparison is the pointwise abutment map. -/
@[simp, stacks 015J "first-filtered abutment comparison of Cartan-Eilenberg resolutions"]
theorem filteredTotalHomologyIso_hom_app (n : ℤ) (X : Bundled A) :
    (filteredTotalHomologyIso F Q n).hom.app X =
      (CartanEilenbergResolution.First.filteredTotalHomologyIso
        X.resolution F Q n).hom := sorry

/-- The inverse component of the first-filtered comparison is the inverse pointwise
abutment map. -/
@[simp, stacks 015J "first-filtered abutment comparison of Cartan-Eilenberg resolutions"]
theorem filteredTotalHomologyIso_inv_app (n : ℤ) (X : Bundled A) :
    (filteredTotalHomologyIso F Q n).inv.app X =
      (CartanEilenbergResolution.First.filteredTotalHomologyIso
        X.resolution F Q n).inv := sorry

/-- Inverse naturality of the first-filtered abutment comparison. -/
@[reassoc, stacks 015J "inverse naturality of the first-filtered abutment comparison"]
theorem filteredTotalHomologyIso_inv_naturality (n : ℤ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (derivedHomology F Q n).map f ≫ (filteredTotalHomologyIso F Q n).inv.app Y =
      (filteredTotalHomologyIso F Q n).inv.app X ≫ (filteredTotalHomology F n).map f := sorry

/-- Conjugating a first-filtered cohomology map by the abutment comparison recovers the source map.
-/
@[reassoc, stacks 015J "source-map computation for the first-filtered abutment comparison"]
theorem filteredTotalHomologyIso_source_map (n : ℤ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (filteredTotalHomologyIso F Q n).hom.app X ≫
        (derivedHomology F Q n).map f ≫
      (filteredTotalHomologyIso F Q n).inv.app Y =
      (filteredTotalHomology F n).map f := sorry

/-- Conjugating a first-filtered map by the inverse abutment comparison recovers the target map. -/
@[reassoc, stacks 015J "target-map computation for the first-filtered abutment comparison"]
theorem filteredTotalHomologyIso_target_map (n : ℤ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (filteredTotalHomologyIso F Q n).inv.app X ≫
        (filteredTotalHomology F n).map f ≫
      (filteredTotalHomologyIso F Q n).hom.app Y =
      (derivedHomology F Q n).map f := sorry

end First

namespace Second

/-- Naturality of the second-filtered abutment comparison on bundled resolutions. -/
@[reassoc, stacks 015J "naturality of the second-filtered abutment comparison"]
theorem filteredTotalHomologyIso_naturality (n : ℤ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (filteredTotalHomology F n).map f ≫
        (CartanEilenbergResolution.Second.filteredTotalHomologyIso
          Y.resolution F Q n).hom =
      (CartanEilenbergResolution.Second.filteredTotalHomologyIso
        X.resolution F Q n).hom ≫ (derivedHomology F Q n).map f := sorry

/-- The second-filtered abutment comparison as a natural isomorphism. -/
@[stacks 015J "second-filtered abutment comparison of Cartan-Eilenberg resolutions"]
noncomputable def filteredTotalHomologyIso (n : ℤ) :
    filteredTotalHomology F n ≅ derivedHomology F Q n :=
  NatIso.ofComponents
    (fun X => CartanEilenbergResolution.Second.filteredTotalHomologyIso
      X.resolution F Q n)
    (filteredTotalHomologyIso_naturality F Q n)

/-- The forward component of the second-filtered comparison is the pointwise abutment map. -/
@[simp, stacks 015J "second-filtered abutment comparison of Cartan-Eilenberg resolutions"]
theorem filteredTotalHomologyIso_hom_app (n : ℤ) (X : Bundled A) :
    (filteredTotalHomologyIso F Q n).hom.app X =
      (CartanEilenbergResolution.Second.filteredTotalHomologyIso
        X.resolution F Q n).hom := sorry

/-- The inverse component of the second-filtered comparison is the inverse pointwise
abutment map. -/
@[simp, stacks 015J "second-filtered abutment comparison of Cartan-Eilenberg resolutions"]
theorem filteredTotalHomologyIso_inv_app (n : ℤ) (X : Bundled A) :
    (filteredTotalHomologyIso F Q n).inv.app X =
      (CartanEilenbergResolution.Second.filteredTotalHomologyIso
        X.resolution F Q n).inv := sorry

/-- Inverse naturality of the second-filtered abutment comparison. -/
@[reassoc, stacks 015J "inverse naturality of the second-filtered abutment comparison"]
theorem filteredTotalHomologyIso_inv_naturality (n : ℤ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (derivedHomology F Q n).map f ≫ (filteredTotalHomologyIso F Q n).inv.app Y =
      (filteredTotalHomologyIso F Q n).inv.app X ≫ (filteredTotalHomology F n).map f := sorry

/-- Conjugating a second-filtered cohomology map by the abutment comparison recovers the source
map. -/
@[reassoc, stacks 015J "source-map computation for the second-filtered abutment comparison"]
theorem filteredTotalHomologyIso_source_map (n : ℤ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (filteredTotalHomologyIso F Q n).hom.app X ≫
        (derivedHomology F Q n).map f ≫
      (filteredTotalHomologyIso F Q n).inv.app Y =
      (filteredTotalHomology F n).map f := sorry

/-- Conjugating a second-filtered map by the inverse abutment comparison recovers the target map.
-/
@[reassoc, stacks 015J "target-map computation for the second-filtered abutment comparison"]
theorem filteredTotalHomologyIso_target_map (n : ℤ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (filteredTotalHomologyIso F Q n).inv.app X ≫
        (filteredTotalHomology F n).map f ≫
      (filteredTotalHomologyIso F Q n).hom.app Y =
      (derivedHomology F Q n).map f := sorry

end Second

end CochainComplex.CartanEilenbergResolution.Bundled
