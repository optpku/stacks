module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Construction
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Projections

/-!
# Binary products of categories fibred in groupoids

The product of two categories fibred in groupoids over `C` is the 2-fibre product of their
canonical projections to the identity fibration. A pair of 1-morphisms induces a product
1-morphism, and relative representability is stable under this construction.
-/

@[expose] public section

open CategoryTheory
open Bicategory
open scoped Bicategory

universe u v

namespace CategoryTheory.FiberedCategoryOver.Groupoids

variable {C : Type u} [Category.{v} C]

/-- The binary product of categories fibred in groupoids over `C`, realized as the 2-fibre
product of their canonical projections to the identity fibration. -/
abbrev prod (X Y : FiberedCategoryOver.Groupoids.{u, v, max u v, v} C) :
    FiberedCategoryOver.Groupoids.{u, v, max u v, v} C :=
  TwoFibreProduct.apex X.baseProjection Y.baseProjection

variable {X Y X₁ X₂ Y₁ Y₂ : FiberedCategoryOver.Groupoids.{u, v, max u v, v} C}

/-- The whiskered projection comparison of a 1-morphism lifts the identity on the base. -/
theorem baseProjection.naturality.isHomLift (f : X ⟶ Y) (a : X.total) :
    Functor.IsHomLift (base C).p (𝟙 (X.p.obj a))
      ((Functor.isoWhiskerRight (commIso f) (baseSection C)).hom.app a) := sorry

/-- A 1-morphism of categories fibred in groupoids is compatible with the canonical projections
to the identity fibration. -/
noncomputable def baseProjection.naturality (f : X ⟶ Y) :
    f ≫ baseProjection Y ≅ baseProjection X :=
  BasedFunctorIso.lift
    (BasedNatIso.mkNatIso
      (Functor.isoWhiskerRight (commIso f) (baseSection C))
      (baseProjection.naturality.isHomLift f))

/-- The identity-base cospan transformation associated to a pair of 1-morphisms of categories
fibred in groupoids. -/
noncomputable def prodMap.cospan (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    CospanTransform X₁.baseProjection X₂.baseProjection
      Y₁.baseProjection Y₂.baseProjection :=
  CospanTransform.mk f₁ f₂ (𝟙 (base C))
    (baseProjection.naturality f₁ ≪≫ (ρ_ _).symm)
    (baseProjection.naturality f₂ ≪≫ (ρ_ _).symm)

/-- The product of 1-morphisms of categories fibred in groupoids, as a 1-morphism
`prod X₁ X₂ ⟶ prod Y₁ Y₂`. -/
noncomputable def prodMap (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    prod X₁ X₂ ⟶ prod Y₁ Y₂ :=
  TwoFibreProduct.map (prodMap.cospan f₁ f₂)

/-- The product 1-morphism commutes with first projections up to the canonical invertible
2-cell. -/
noncomputable def prodMap.fstIso (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    prodMap f₁ f₂ ≫ TwoFibreProduct.fst Y₁.baseProjection Y₂.baseProjection ≅
      TwoFibreProduct.fst X₁.baseProjection X₂.baseProjection ≫ f₁ :=
  TwoFibreProduct.map.fstIso (prodMap.cospan f₁ f₂)

/-- The product 1-morphism commutes with second projections up to the canonical invertible
2-cell. -/
noncomputable def prodMap.sndIso (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    prodMap f₁ f₂ ≫ TwoFibreProduct.snd Y₁.baseProjection Y₂.baseProjection ≅
      TwoFibreProduct.snd X₁.baseProjection X₂.baseProjection ≫ f₂ :=
  TwoFibreProduct.map.sndIso (prodMap.cospan f₁ f₂)

/-- Relative representability of 1-morphisms of categories fibred in groupoids is stable under
binary products. -/
theorem relativelyRepresentable.prod_map {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
    (hf₁ : relativelyRepresentable f₁) (hf₂ : relativelyRepresentable f₂) :
    relativelyRepresentable (prodMap f₁ f₂) := sorry

end CategoryTheory.FiberedCategoryOver.Groupoids
