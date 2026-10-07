module

public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.PrincipalSeg

/-!
# Extending a preorder diagram through a closed cut

Given a functor on `Set.Iio j` and a cocone over it, this file constructs the
functor on `Set.Iic j` obtained by adjoining the cocone point.  Equivalent
maximal indices in a preorder are all sent to the same point, so no
antisymmetry or linearity assumption is needed.
-/

@[expose] public section

universe u v w

namespace CategoryTheory.Limits.Cocone

open Category

variable {C : Type u} [Category.{v} C]
variable {I : Type w} [Preorder I]
variable {j : I} {F : Set.Iio j ⥤ C}

namespace toIic

/-- The object of the closed extension at one preorder index. -/
noncomputable def obj (c : Cocone F) (i : I) : C :=
  open Classical in
  if hi : i < j then F.obj ⟨i, hi⟩ else c.pt

/-- The canonical comparison with the original object below the cut. -/
noncomputable def objIso (c : Cocone F) (i : I) (hi : i < j) :
    obj c i ≅ F.obj ⟨i, hi⟩ :=
  open Classical in
  eqToIso (dif_pos hi)

/-- The canonical comparison with the cocone point at an index that is not
strictly below the cut. -/
noncomputable def objIsoPt (c : Cocone F) (i : I) (hi : ¬ i < j) :
    obj c i ≅ c.pt :=
  open Classical in
  eqToIso (dif_neg hi)

/-- The morphism of the closed extension along one preorder comparison. -/
noncomputable def map (c : Cocone F) (i₁ i₂ : I) (h₁₂ : i₁ ≤ i₂) :
    obj c i₁ ⟶ obj c i₂ :=
  open Classical in
  if h₂ : i₂ < j then
    (objIso c i₁ (lt_of_le_of_lt h₁₂ h₂)).hom ≫
      F.map (homOfLE h₁₂) ≫ (objIso c i₂ h₂).inv
  else if h₁ : i₁ < j then
    (objIso c i₁ h₁).hom ≫ c.ι.app ⟨i₁, h₁⟩ ≫
      (objIsoPt c i₂ h₂).inv
  else
    (objIsoPt c i₁ h₁).hom ≫ (objIsoPt c i₂ h₂).inv

/-- The closed-extension map at a reflexive comparison is an identity. -/
theorem map_id (c : Cocone F) (i : I) :
    map c i i le_rfl = 𝟙 _ := sorry

/-- Closed-extension maps compose along chains in the indexing preorder. -/
theorem map_comp (c : Cocone F) (i₁ i₂ i₃ : I)
    (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃) :
    map c i₁ i₃ (h₁₂.trans h₂₃) =
      map c i₁ i₂ h₁₂ ≫ map c i₂ i₃ h₂₃ := sorry

end toIic

/-- Extend a strict-predecessor functor through the corresponding closed cut
using a chosen cocone. -/
noncomputable def toIic (c : Cocone F) : Set.Iic j ⥤ C where
  obj i := toIic.obj c i.1
  map f := toIic.map c _ _ (leOfHom f)
  map_id i := toIic.map_id c i.1
  map_comp f g := toIic.map_comp c _ _ _ (leOfHom f) (leOfHom g)

end CategoryTheory.Limits.Cocone
