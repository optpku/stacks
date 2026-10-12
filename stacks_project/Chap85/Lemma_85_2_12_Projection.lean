/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Lemma_85_2_1_Opens
public import stacks_project.Chap85.Lemma_85_2_1_Site
public import stacks_project.Chap85.Lemma_85_2_5_Component

/-!
# Degree-forgetting projection of a constant simplicial Zariski site

For a topological space `X` viewed as a constant simplicial space, the forget-degree
functor `U ↦ U` from `X_{•,Zar}` to `X_Zar`, together with the associated cosimplicial
assembly of degreewise restrictions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped Simplicial

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject

/-- The constant simplicial topological space with value `X`. -/
abbrev constSpace (X : TopCat.{u}) : SimplicialObject TopCat.{u} :=
  (const TopCat.{u}).obj X

/-- The constant simplicial space evaluates to `X` in every degree. -/
theorem constSpace_obj (X : TopCat.{u}) (n : SimplexCategoryᵒᵖ) :
    (constSpace X).obj n = X :=
  sorry

/-- The degree-forgetting functor `X_{•,Zar} ⥤ X_Zar`, `U ↦ U`. -/
def constProjection (X : TopCat.{u}) : zariskiSite (constSpace X) ⥤ Opens X where
  obj U := U.opens
  map f := homOfLE fun x hx ↦ f.mapsTo hx
  map_id := sorry
  map_comp := sorry

/-- The object map of `constProjection` is the underlying open of a diagram open. -/
theorem constProjection_obj (X : TopCat.{u}) (U : zariskiSite (constSpace X)) :
    (constProjection X).obj U = U.opens :=
  sorry

/-- Identity-stage maps of the constant simplicial space are open inclusions. -/
theorem constProjection_map (X : TopCat.{u}) {U V : zariskiSite (constSpace X)} (f : U ⟶ V) :
    (constProjection X).map f = homOfLE fun x hx ↦ f.mapsTo hx :=
  sorry

/-- The degree-forgetting functor is continuous. -/
instance constProjection_isContinuous (X : TopCat.{u}) :
    (constProjection X).IsContinuous (zariskiTopology (constSpace X))
      (Opens.grothendieckTopology X) :=
  sorry

/-- The degree-forgetting functor is cocontinuous. -/
instance constProjection_isCocontinuous (X : TopCat.{u}) :
    (constProjection X).IsCocontinuous (zariskiTopology (constSpace X))
      (Opens.grothendieckTopology X) :=
  sorry

/-- Degree-`c` inclusion of the constant simplicial space is continuous. -/
instance constSpace_fiber_isContinuous (X : TopCat.{u}) (c : SimplexCategoryᵒᵖ) :
    (DiagramOpens.fiber (constSpace X) c).IsContinuous
      (Opens.grothendieckTopology (X : Type u)) (zariskiTopology (constSpace X)) :=
  sorry

/-- Degree-`n` component inclusion of the constant simplicial space is continuous. -/
instance constSpace_component_isContinuous (X : TopCat.{u}) (n : ℕ) :
    (component (constSpace X) n).IsContinuous
      (Opens.grothendieckTopology ((constSpace X).obj (op ⦋n⦌)))
      (zariskiTopology (constSpace X)) :=
  sorry

/-- Degree-`c` inclusion of the constant simplicial space is cocontinuous. -/
instance constSpace_fiber_isCocontinuous (X : TopCat.{u}) (c : SimplexCategoryᵒᵖ) :
    (DiagramOpens.fiber (constSpace X) c).IsCocontinuous
      (Opens.grothendieckTopology (X : Type u)) (zariskiTopology (constSpace X)) :=
  sorry

/-- Degree-`n` component inclusion of the constant simplicial space is cocontinuous. -/
instance constSpace_component_isCocontinuous (X : TopCat.{u}) (n : ℕ) :
    (component (constSpace X) n).IsCocontinuous
      (Opens.grothendieckTopology ((constSpace X).obj (op ⦋n⦌)))
      (zariskiTopology (constSpace X)) :=
  sorry

/-- Forget-degree after degree-`c` inclusion is a continuous endofunctor of `Opens X`. -/
instance constSpace_fiber_comp_constProjection_isContinuous
    (X : TopCat.{u}) (c : SimplexCategoryᵒᵖ) :
    (DiagramOpens.fiber (constSpace X) c ⋙ constProjection X).IsContinuous
      (Opens.grothendieckTopology (X : Type u))
      (Opens.grothendieckTopology (X : Type u)) :=
  sorry

/-- The natural transformation of degree-`c` inclusions induced by a simplex operator. -/
def fiberStageNT (X : TopCat.{u}) {c d : SimplexCategoryᵒᵖ} (f : c ⟶ d) :
    DiagramOpens.fiber (constSpace X) c ⟶ DiagramOpens.fiber (constSpace X) d where
  app U := DiagramOpens.homMk f fun x hx ↦ hx
  naturality := sorry

/-- Identity simplex operators induce identity fiber-stage natural transformations. -/
theorem fiberStageNT_id (X : TopCat.{u}) (c : SimplexCategoryᵒᵖ) :
    fiberStageNT X (𝟙 c) = 𝟙 (DiagramOpens.fiber (constSpace X) c) :=
  sorry

/-- Fiber-stage natural transformations are functorial in simplex operators. -/
theorem fiberStageNT_comp (X : TopCat.{u}) {c d e : SimplexCategoryᵒᵖ} (f : c ⟶ d) (g : d ⟶ e) :
    @fiberStageNT X c e (f ≫ g) = @fiberStageNT X c d f ≫ @fiberStageNT X d e g :=
  sorry

/-- Degree-`c` inclusion followed by forget-degree is the identity on `Opens X`. -/
def fiber_comp_constProjection (X : TopCat.{u}) (c : SimplexCategoryᵒᵖ) :
    DiagramOpens.fiber (constSpace X) c ⋙ constProjection X ≅ 𝟭 (Opens X) where
  hom := { app := fun _ ↦ 𝟙 _, naturality := sorry }
  inv := { app := fun _ ↦ 𝟙 _, naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underlying cosimplicial object of `toCosimplicial` on a single sheaf. -/
def toCosimplicialObj (X : TopCat.{u}) {A : Type (u + 1)} [Category.{u} A]
    (F : Sheaf (zariskiTopology (constSpace X)) A) :
    CosimplicialObject (Sheaf (Opens.grothendieckTopology X) A) where
  obj n := (sheafComponent (constSpace X) n.len A).obj F
  map {n m} f :=
    ObjectProperty.homMk
      (whiskerRight (NatTrans.op (@fiberStageNT X (op m) (op n) f.op)) F.obj)
  map_id := sorry
  map_comp := sorry

/-- A sheaf on `X_{•,Zar}` determines a cosimplicial sheaf on `X` by restriction to each
degree. -/
def toCosimplicial (X : TopCat.{u}) (A : Type (u + 1)) [Category.{u} A] :
    Sheaf (zariskiTopology (constSpace X)) A ⥤
      CosimplicialObject (Sheaf (Opens.grothendieckTopology X) A) where
  obj F := toCosimplicialObj X F
  map α :=
    { app := fun n ↦ (sheafComponent (constSpace X) n.len A).map α
      naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- On objects, `toCosimplicial` evaluates as the degree-`n` component. -/
theorem toCosimplicial_obj (X : TopCat.{u}) {A : Type (u + 1)} [Category.{u} A]
    (F : Sheaf (zariskiTopology (constSpace X)) A) (n : SimplexCategory) :
    ((toCosimplicial X A).obj F).obj n = (sheafComponent (constSpace X) n.len A).obj F :=
  sorry

/-- Coface maps of `toCosimplicial.obj F` are the degree maps associated to
`SimplexCategory.δ`. -/
theorem toCosimplicial_δ (X : TopCat.{u}) {A : Type (u + 1)} [Category.{u} A]
    (F : Sheaf (zariskiTopology (constSpace X)) A) {n : ℕ} (i : Fin (n + 2)) :
    ((toCosimplicial X A).obj F).δ i =
      ((toCosimplicial X A).obj F).map (SimplexCategory.δ i) :=
  sorry

end CategoryTheory.SimplicialObject
