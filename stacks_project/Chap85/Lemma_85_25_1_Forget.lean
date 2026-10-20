module

public import ReasLib.Topology.Category.LCCat.Simplicial
public import ReasLib.Topology.Category.TopCat.DiagramOpens.Constant

/-! # Underlying simplicial spaces and augmentations -/

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialObject

universe u

namespace LCCat

variable (U : SimplicialObject LCCat.{u}) (X : LCCat.{u})

#check (LCCat.forgetToTop : SimplicialObject LCCat.{u} ⥤ SimplicialObject TopCat.{u})
#check (LCCat.forgetToTop_obj U : forgetToTop.obj U = U ⋙ toTopCat)
#check (LCCat.forgetToTop_const X :
  forgetToTop.obj ((SimplicialObject.const LCCat.{u}).obj X) ≅ constSpace X.obj)
#check (LCCat.forgetToTop_const_app X : ∀ n : SimplexCategoryᵒᵖ,
  (forgetToTop_const X).app n = Iso.refl _)

variable (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X)

#check (LCCat.toTopCatAugmentation a : forgetToTop.obj U ⟶ constSpace X.obj)
#check (LCCat.toTopCatAugmentation_def a :
  toTopCatAugmentation a = forgetToTop.map a ≫ (forgetToTop_const X).hom)

end LCCat
