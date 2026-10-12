/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Presheaf
public import ReasLib.CategoryTheory.Sites.CategoryHomology.Bar
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Chain-level fiber bar complexes

The homology presheaf of a fibered category is obtained from a chain complex of presheaves on the
base.  This leaf owns that chain-level construction; sheafification and delta-functor packaging
are layered on top of it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v wX vX w

namespace CategoryTheory.FiberedCategoryOver.FiberHomology.Bar

variable {C : Type u} [Category.{v} C]
variable (X : FiberedCategoryOver.{u, v, wX, vX} C)
variable [UnivLE.{max wX vX, w}]

/-- The chain map on fiber Bar complexes induced by a cartesian lift over a base arrow. -/
@[stacks 08PI "fiber bar complex restriction map"]
noncomputable abbrev complexRestriction
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w})
    {U V : C} (f : V ⟶ U) :
    CategoryHomology.complex
        (Presheaf.restrict X AddCommGrpCat.{w} F U) ⟶
      CategoryHomology.complex
        (Presheaf.restrict X AddCommGrpCat.{w} F V) :=
  CategoryHomology.complexMap
    ((Functor.Cleavage.ofIsFibered X.p).reindex f)
    (Presheaf.cartesianRestriction X AddCommGrpCat.{w} F f)

/-- The degree-`n` presheaf of chains in the fiber Bar construction. -/
@[stacks 08PI "fiber bar complex degree presheaf"]
noncomputable def complexDegree
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj V :=
    (CategoryHomology.complex
      (Presheaf.restrict X AddCommGrpCat.{w} F V.unop)).X n
  map f :=
    (complexRestriction X F f.unop).f n
  map_id := sorry
  map_comp := sorry

/-- The chain complex of base presheaves whose homology is fiberwise Bar homology. -/
@[stacks 08PI "fiber bar complex presheaf"]
noncomputable def complexPresheaf
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) :
    ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ℕ where
  X n := complexDegree X F n
  d n m :=
    { app V :=
        (CategoryHomology.complex
          (Presheaf.restrict X AddCommGrpCat.{w} F V.unop)).d n m
      naturality := fun {_ _} f ↦ by sorry }
  shape := by sorry
  d_comp_d' := by sorry

/-- The chain-level map induced by a morphism of total coefficient presheaves. -/
@[stacks 08PI "fiber bar complex coefficient map"]
noncomputable def complexMap
    {F G : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}} (τ : F ⟶ G) :
    complexPresheaf X F ⟶ complexPresheaf X G where
  f n :=
    { app V :=
        (CategoryHomology.complexMap
          (𝟭 (X.p.Fiber V.unop))
          (Presheaf.restrictMap X AddCommGrpCat.{w} τ V.unop)).f n
      naturality := fun {_ _} f ↦ by sorry }
  comm' := by sorry

/-- The fiber Bar chain complex as a functor of total coefficient presheaves. -/
@[stacks 08PI "fiber bar complex coefficient functor"]
noncomputable def complexFunctor :
    (X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤
      ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ℕ where
  obj F := complexPresheaf X F
  map τ := complexMap X τ
  map_id := sorry
  map_comp := sorry

/-- The fiber Bar chain-complex coefficient functor is additive. -/
@[stacks 08PI "additivity of fiber bar complex coefficient functor"]
instance complexFunctor.additive : (complexFunctor X).Additive := sorry

/-- Evaluation of the fiber Bar chain-complex functor on a coefficient presheaf. -/
@[simp, stacks 08PI "fiber bar chain-complex functor object formula"]
theorem complexFunctor_obj
    (F : CategoryTheory.Functor X.totalᵒᵖ AddCommGrpCat.{w}) :
    (complexFunctor X).obj F = complexPresheaf X F := sorry

/-- Evaluation of the fiber Bar chain-complex functor on a coefficient morphism. -/
@[simp, stacks 08PI "fiber bar chain-complex functor map formula"]
theorem complexFunctor_map
    {F G : CategoryTheory.Functor X.totalᵒᵖ AddCommGrpCat.{w}}
    (t : NatTrans F G) :
    (complexFunctor X).map t = complexMap X t := sorry

/-- Evaluating the fiber Bar complex at a base object gives the ordinary fiber Bar complex. -/
@[simp, stacks 08PI "fiber bar complex evaluation"]
theorem complexDegree_obj
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) (V : Cᵒᵖ) :
    (complexDegree X F n).obj V =
      (CategoryHomology.complex
        (Presheaf.restrict X AddCommGrpCat.{w} F V.unop)).X n := rfl

end CategoryTheory.FiberedCategoryOver.FiberHomology.Bar
