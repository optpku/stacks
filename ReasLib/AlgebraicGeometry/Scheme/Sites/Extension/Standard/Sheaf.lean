/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Sites.Small
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Standard
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Zariski

/-!
# Standard-cover sheaf extensions

This leaf translates a finite affine family of arrows in a full subcategory of
`Over S` into a standard-cover test and proves the corresponding sheaf
extension interface. Directed-limit descent of covers belongs to the sibling
`Standard.Descent` leaf.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty

universe u v

namespace AlgebraicGeometry

noncomputable section

namespace StandardTopology

/-- The Grothendieck topology on `Over S` selected by a standard topology. -/
abbrev overTopology (τ : StandardTopology) (S : Scheme.{u}) :
    GrothendieckTopology (Over S) :=
  match τ with
  | zariski => Scheme.zariskiTopology.over S
  | etale => S.overGrothendieckTopology @Etale
  | smooth => S.overGrothendieckTopology @Smooth
  | syntomic => S.overGrothendieckTopology (@Syntomic)
  | fppf => Scheme.fppfTopology.over S

/-- The Zariski member of `overTopology` is the usual big Zariski topology. -/
theorem overTopology_zariski (S : Scheme.{u}) :
    overTopology zariski S = Scheme.zariskiTopology.over S := sorry

namespace Affine

/-- The finite affine family induced by a finite family of arrows in a full
subcategory of `Over S`. -/
def coverFamily {S : Scheme.{u}} (C : ObjectProperty (Over S))
    {n : ℕ} {X : C.FullSubcategory} (U : Fin n → C.FullSubcategory)
    (f : ∀ i, U i ⟶ X)
    (hU_affine : ∀ i, IsAffine ((U i).obj : Over S).left) :
    AffineFamilyOver ((X.obj : Over S).left) where
  n := n
  U := fun i ↦ ((U i).obj : Over S).left
  map := fun i ↦ (f i).hom.left
  isAffine := hU_affine

/-- The chart map of `coverFamily` is the underlying scheme map of the
corresponding arrow in the full subcategory. -/
@[simp]
theorem coverFamily_map {S : Scheme.{u}} (C : ObjectProperty (Over S))
    {n : ℕ} {X : C.FullSubcategory} (U : Fin n → C.FullSubcategory)
    (f : ∀ i, U i ⟶ X)
    (hU_affine : ∀ i, IsAffine ((U i).obj : Over S).left) (i : Fin n) :
    (coverFamily C U f hU_affine).map i = (f i).hom.left := sorry

/-- A presheaf on a full subcategory satisfies the finite affine standard
cover sheaf condition on objects with an affine presentation. -/
def IsSheaf {S : Scheme.{u}} (C : ObjectProperty (Over S))
    (τ : StandardTopology) (F : C.FullSubcategoryᵒᵖ ⥤ Type v) : Prop :=
  ∀ {n : ℕ} {X : C.FullSubcategory} (U : Fin n → C.FullSubcategory)
    (f : ∀ i, U i ⟶ X)
    (hU_affine : ∀ i, IsAffine ((U i).obj : Over S).left),
      Scheme.Over.HasAffinePresentation (X.obj : Over S) →
        τ.IsCover (coverFamily C U f hU_affine) →
          Presieve.IsSheafFor F (Presieve.ofArrows U f)

/-- The finite affine standard-cover sheaf condition unfolds to its covering
family form. -/
theorem isSheaf_iff {S : Scheme.{u}} (C : ObjectProperty (Over S))
    (τ : StandardTopology) (F : C.FullSubcategoryᵒᵖ ⥤ Type v) :
    IsSheaf C τ F ↔
      ∀ {n : ℕ} {X : C.FullSubcategory} (U : Fin n → C.FullSubcategory)
        (f : ∀ i, U i ⟶ X)
        (hU_affine : ∀ i, IsAffine ((U i).obj : Over S).left),
          Scheme.Over.HasAffinePresentation (X.obj : Over S) →
            τ.IsCover (coverFamily C U f hU_affine) →
              Presieve.IsSheafFor F (Presieve.ofArrows U f) := sorry

/-- A Zariski extension satisfying the standard finite-affine cover test is
a sheaf for the selected standard topology. -/
theorem extension_isSheaf
    {S : Scheme.{u}} (C : ObjectProperty (Over S))
    (F : C.FullSubcategoryᵒᵖ ⥤ Type v) (F' : (Over S)ᵒᵖ ⥤ Type v)
    (hC_open : Scheme.Over.Extension.ContainsAffineOpens C)
    (hC_fp : Scheme.Over.Extension.ContainsFinitelyPresentedAffines C)
    (hF_zariski : Scheme.Over.Extension.IsZariskiSheaf C F)
    (hF_limits : Scheme.Over.Extension.PreservesDirectedAffineLimits C F)
    (eF' : C.ι.op ⋙ F' ≅ F)
    (hF'_zariski : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F')
    (hF'_limits : Scheme.Over.PreservesDirectedAffineLimits S F')
    (hF'_unique :
      ∀ (G : (Over S)ᵒᵖ ⥤ Type v) (eG : C.ι.op ⋙ G ≅ F),
        Presheaf.IsSheaf (Scheme.zariskiTopology.over S) G →
        Scheme.Over.PreservesDirectedAffineLimits S G →
        ∃! α : F' ≅ G, Functor.isoWhiskerLeft C.ι.op α ≪≫ eG = eF')
    (τ : StandardTopology) (hF_standard : IsSheaf C τ F) :
    Presheaf.IsSheaf (τ.overTopology S) F' := sorry

end Affine

/-- A sheaf on a full subcategory for a standard topology has a sheaf extension
when the extension is the unique Zariski sheaf extension preserving directed
affine limits. -/
theorem extension_isSheaf_of_isSheaf
    {S : Scheme.{u}} (τ : StandardTopology) (C : ObjectProperty (Over S))
    (F : C.FullSubcategoryᵒᵖ ⥤ Type v) (F' : (Over S)ᵒᵖ ⥤ Type v)
    (hC_open : Scheme.Over.Extension.ContainsAffineOpens C)
    (hC_fp : Scheme.Over.Extension.ContainsFinitelyPresentedAffines C)
    (hF_tau : Presheaf.IsSheaf (C.ι.restrictedTopology (τ.overTopology S)) F)
    (hF_limits : Scheme.Over.Extension.PreservesDirectedAffineLimits C F)
    (eF' : C.ι.op ⋙ F' ≅ F)
    (hF'_zariski : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F')
    (hF'_limits : Scheme.Over.PreservesDirectedAffineLimits S F')
    (hF'_unique :
      ∀ (G : (Over S)ᵒᵖ ⥤ Type v) (eG : C.ι.op ⋙ G ≅ F),
        Presheaf.IsSheaf (Scheme.zariskiTopology.over S) G →
        Scheme.Over.PreservesDirectedAffineLimits S G →
        ∃! α : F' ≅ G, Functor.isoWhiskerLeft C.ι.op α ≪≫ eG = eF') :
    Presheaf.IsSheaf (τ.overTopology S) F' := sorry

end StandardTopology

end

end AlgebraicGeometry
