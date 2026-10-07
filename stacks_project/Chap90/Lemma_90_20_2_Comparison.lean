module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Construction
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Construction
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Projections
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal
public import stacks_project.Chap90.Remarks_90_5_2_Groupoids

/-!
# Identity-leg maps of 2-fibre products

Postcomposing a cospan of categories cofibered in groupoids with a further 1-morphism
induces the comparison `H1 ×_G H2 ⟶ H1 ×_F H2`.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open Bicategory
open CofiberedCategoryOver.Groupoids
open scoped Bicategory
open scoped CategoryTheory.Bicategory.CospanTransform

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {H1 H2 G F :
    CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k)}

namespace CategoryTheory.TwoFibreProduct

/-- The identity-leg cospan transformation with base `q`, sending the cospan `p1, p2`
to `p1 ≫ q, p2 ≫ q`. -/
noncomputable def postcomposeCospan (p1 : H1 ⟶ G) (p2 : H2 ⟶ G) (q : G ⟶ F) :
    CospanTransform p1 p2 (p1 ≫ q) (p2 ≫ q) :=
  CospanTransform.mk (𝟙 H1) (𝟙 H2) q (λ_ (p1 ≫ q)) (λ_ (p2 ≫ q))

/-- The left vertex of `postcomposeCospan p1 p2 q` is the identity of `H1`. -/
theorem postcomposeCospan_left (p1 : H1 ⟶ G) (p2 : H2 ⟶ G) (q : G ⟶ F) :
    (postcomposeCospan p1 p2 q).left = 𝟙 H1 := sorry

/-- The right vertex of `postcomposeCospan p1 p2 q` is the identity of `H2`. -/
theorem postcomposeCospan_right (p1 : H1 ⟶ G) (p2 : H2 ⟶ G) (q : G ⟶ F) :
    (postcomposeCospan p1 p2 q).right = 𝟙 H2 := sorry

/-- The base vertex of `postcomposeCospan p1 p2 q` is `q`. -/
theorem postcomposeCospan_base (p1 : H1 ⟶ G) (p2 : H2 ⟶ G) (q : G ⟶ F) :
    (postcomposeCospan p1 p2 q).base = q := sorry

/-- The comparison 1-morphism `H1 ×_G H2 ⟶ H1 ×_F H2` induced by postcomposing the
cospan legs with `q`. -/
noncomputable def mapPostcompose (p1 : H1 ⟶ G) (p2 : H2 ⟶ G) (q : G ⟶ F) :
    apex.{u + 1, u, u + 1, u} p1 p2 ⟶ apex.{u + 1, u, u + 1, u} (p1 ≫ q) (p2 ≫ q) :=
  map (postcomposeCospan p1 p2 q)

/-- `mapPostcompose p1 p2 q` is the two-fibre-product map of `postcomposeCospan p1 p2 q`. -/
theorem mapPostcompose_eq_map (p1 : H1 ⟶ G) (p2 : H2 ⟶ G) (q : G ⟶ F) :
    mapPostcompose p1 p2 q = map (postcomposeCospan p1 p2 q) := sorry

/-- The comparison 1-morphism commutes with first projections up to the canonical
invertible cell and the right unitor. -/
noncomputable def mapPostcompose_fst (p1 : H1 ⟶ G) (p2 : H2 ⟶ G) (q : G ⟶ F) :
    mapPostcompose p1 p2 q ≫ fst (p1 ≫ q) (p2 ≫ q) ≅ fst p1 p2 :=
  map.fstIso (postcomposeCospan p1 p2 q) ≪≫ ρ_ (fst p1 p2)

/-- The comparison 1-morphism commutes with second projections up to the canonical
invertible cell and the right unitor. -/
noncomputable def mapPostcompose_snd (p1 : H1 ⟶ G) (p2 : H2 ⟶ G) (q : G ⟶ F) :
    mapPostcompose p1 p2 q ≫ snd (p1 ≫ q) (p2 ≫ q) ≅ snd p1 p2 :=
  map.sndIso (postcomposeCospan p1 p2 q) ≪≫ ρ_ (snd p1 p2)

end CategoryTheory.TwoFibreProduct
