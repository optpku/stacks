/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation

/-!
# Conditions for extending sheaves from scheme subcategories

This module packages the affine-open, finite-presentation, sheaf, and
directed-affine-limit conditions that occur when a presheaf on a full
subcategory of `Over S` is extended to all schemes over `S`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty

universe u v w

namespace AlgebraicGeometry

namespace Scheme.Over

/-- An object of `Over S` has an affine-open factorization with a locally
finitely presented map to that affine open. -/
def HasAffinePresentation {S : Scheme.{u}} (X : Over S) : Prop :=
  ∃ U : S.Opens, IsAffineOpen U ∧
    ∃ g : X.left ⟶ (U : Scheme.{u}), LocallyOfFinitePresentation g ∧
      g ≫ U.ι = X.hom

/-- The affine-presentation condition unfolds to its chosen open and map. -/
theorem hasAffinePresentation_iff {S : Scheme.{u}} (X : Over S) :
    HasAffinePresentation X ↔
      ∃ U : S.Opens, IsAffineOpen U ∧
        ∃ g : X.left ⟶ (U : Scheme.{u}), LocallyOfFinitePresentation g ∧
          g ≫ U.ι = X.hom := sorry

end Scheme.Over

namespace Scheme.Over.Extension

/-- A full subcategory of `Over S` contains affine opens of its objects, up to
isomorphism over `S`. -/
def ContainsAffineOpens {S : Scheme.{u}} (C : ObjectProperty (Over S)) : Prop :=
  ∀ (X : C.FullSubcategory) (U : Scheme.Opens (X.obj : Over S).left), IsAffineOpen U →
    ∃ Y : C.FullSubcategory, Nonempty (Over.mk (U.ι ≫ X.obj.hom) ≅ Y.obj)

/-- The affine-open closure condition unfolds to its objectwise form. -/
theorem containsAffineOpens_iff {S : Scheme.{u}}
    (C : ObjectProperty (Over S)) :
    ContainsAffineOpens C ↔
      ∀ (X : C.FullSubcategory) (U : Scheme.Opens (X.obj : Over S).left), IsAffineOpen U →
        ∃ Y : C.FullSubcategory, Nonempty (Over.mk (U.ι ≫ X.obj.hom) ≅ Y.obj) := sorry

/-- A full subcategory of `Over S` contains affine schemes of finite
presentation over affine opens of `S`, up to isomorphism over `S`. -/
def ContainsFinitelyPresentedAffines {S : Scheme.{u}}
    (C : ObjectProperty (Over S)) : Prop :=
  ∀ (U : S.Opens), IsAffineOpen U →
    ∀ (V : Scheme.{u}) [IsAffine V] (g : V ⟶ (U : Scheme.{u})),
      LocallyOfFinitePresentation g →
        ∃ Y : C.FullSubcategory, Nonempty (Over.mk (g ≫ U.ι) ≅ Y.obj)

/-- The finite-presentation affine-over-affine-base closure condition unfolds
to its objectwise form. -/
theorem containsFinitelyPresentedAffines_iff {S : Scheme.{u}}
    (C : ObjectProperty (Over S)) :
    ContainsFinitelyPresentedAffines C ↔
      ∀ (U : S.Opens), IsAffineOpen U →
        ∀ (V : Scheme.{u}) [IsAffine V] (g : V ⟶ (U : Scheme.{u})),
          LocallyOfFinitePresentation g →
            ∃ Y : C.FullSubcategory, Nonempty (Over.mk (g ≫ U.ι) ≅ Y.obj) := sorry

/-- A presheaf on a full subcategory of `Over S` satisfies the Zariski sheaf
condition for every Zariski-covering family internal to that subcategory. -/
def IsZariskiSheaf {S : Scheme.{u}}
    (C : ObjectProperty (Over S)) (F : C.FullSubcategoryᵒᵖ ⥤ Type v) : Prop :=
  ∀ {ι : Type w} {X : C.FullSubcategory} (U : ι → C.FullSubcategory)
    (f : ∀ i, U i ⟶ X),
      Presieve.ofArrows (fun i ↦ (U i).obj) (fun i ↦ (f i).hom) ∈
        (Scheme.zariskiTopology.over S).toPrecoverage X.obj →
      Presieve.IsSheafFor F (Presieve.ofArrows U f)

/-- The Zariski sheaf condition on a full subcategory unfolds to its
covering-family form. -/
theorem isZariskiSheaf_iff {S : Scheme.{u}}
    (C : ObjectProperty (Over S)) (F : C.FullSubcategoryᵒᵖ ⥤ Type v) :
    IsZariskiSheaf C F ↔
      ∀ {ι : Type w} {X : C.FullSubcategory} (U : ι → C.FullSubcategory)
        (f : ∀ i, U i ⟶ X),
          Presieve.ofArrows (fun i ↦ (U i).obj) (fun i ↦ (f i).hom) ∈
            (Scheme.zariskiTopology.over S).toPrecoverage X.obj →
          Presieve.IsSheafFor F (Presieve.ofArrows U f) := sorry

/-- A presheaf on a full subcategory of `Over S` preserves directed limits of
affine schemes whose stages and limit lie in that subcategory. -/
def PreservesDirectedAffineLimits {S : Scheme.{u}}
    (C : ObjectProperty (Over S)) (F : C.FullSubcategoryᵒᵖ ⥤ Type v) : Prop :=
  ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ C.FullSubcategory) (c : Cone D),
      IsLimit ((C.ι).mapCone c) →
      (∀ i : I, IsAffine ((D.obj i).obj : Over S).left) →
      IsAffine (c.pt.obj : Over S).left →
      Nonempty (IsColimit (F.mapCocone c.op))

/-- The directed-affine-limit condition on a full subcategory unfolds to its
diagrammatic form. -/
theorem preservesDirectedAffineLimits_iff {S : Scheme.{u}}
    (C : ObjectProperty (Over S)) (F : C.FullSubcategoryᵒᵖ ⥤ Type v) :
    PreservesDirectedAffineLimits C F ↔
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ C.FullSubcategory) (c : Cone D),
          IsLimit ((C.ι).mapCone c) →
          (∀ i : I, IsAffine ((D.obj i).obj : Over S).left) →
          IsAffine (c.pt.obj : Over S).left →
          Nonempty (IsColimit (F.mapCocone c.op)) := sorry

end Scheme.Over.Extension

end AlgebraicGeometry
