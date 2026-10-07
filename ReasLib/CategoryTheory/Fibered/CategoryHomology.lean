module

public import ReasLib.CategoryTheory.Fibered.Presheaf
public import ReasLib.CategoryTheory.Fibered.Presheaf.FiberwiseColimit.LowerShriek
public import ReasLib.CategoryTheory.Fibered.InheritedTopology
public import ReasLib.CategoryTheory.Sites.CategoryHomology.Bar
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bar category homology along fibers

This leaf owns the hypothesis-light bar-complex presheaf and sheaf constructions for a fibered
category.  The projective-resolution presentation is intentionally isolated in
`ReasLib.CategoryTheory.Fibered.CategoryHomology.Derived`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v wX vX

namespace CategoryTheory.FiberedCategoryOver.FiberHomology.Bar

universe w

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (X : CategoryTheory.FiberedCategoryOver.{u, v, wX, vX} C)
variable [UnivLE.{max wX vX, w}]

/-- The bar-complex homology of a presheaf restricted to one fiber. -/
@[stacks 08PI "bar fiber category homology object"]
noncomputable abbrev homology
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (V : C) (n : ℕ) :
    AddCommGrpCat.{w} :=
  CategoryHomology.Bar.homology (C := X.p.Fiber V)
    (Presheaf.restrict X AddCommGrpCat.{w} F V) n

/-- The bar-homology restriction map induced by a cartesian lift over a base arrow. -/
@[stacks 08PI "bar fiber category homology restriction map"]
noncomputable abbrev restriction
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w})
    {U V : C} (f : V ⟶ U) (n : ℕ) :
    homology X F U n ⟶ homology X F V n :=
  CategoryHomology.Bar.map (C := X.p.Fiber V) (C' := X.p.Fiber U)
    ((Functor.Cleavage.ofIsFibered X.p).reindex f)
    (Presheaf.cartesianRestriction X AddCommGrpCat.{w} F f) n

/-- Bar fiber homology sends identity base arrows to identity maps. -/
@[simp, stacks 08PI "bar fiber homology identity map"]
theorem restriction_id
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) (U : C) :
    restriction X F (𝟙 U) n = 𝟙 (homology X F U n) := sorry

/-- Bar fiber homology respects composition of base arrows. -/
@[simp, stacks 08PI "bar fiber homology composition map"]
theorem restriction_comp
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    restriction X F (g ≫ f) n =
      restriction X F f n ≫ restriction X F g n := sorry

/-- The presheaf whose value at `U` is bar homology of the fiber over `U`. -/
@[stacks 08PI "bar fiber category homology presheaf"]
def presheaf
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj V := homology X F V.unop n
  map f := restriction X F f.unop n
  map_id := fun V => restriction_id X F n V.unop
  map_comp := fun f g => restriction_comp X F n f.unop g.unop

/-- The bar-homology map at a fiber induced by a morphism of total presheaves. -/
@[stacks 08PI "bar fiber homology coefficient map component"]
noncomputable abbrev mapApp
    {F G : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}} (τ : F ⟶ G) (U : C) (n : ℕ) :
    homology X F U n ⟶ homology X G U n :=
  CategoryHomology.Bar.map
    (C := X.p.Fiber U) (C' := X.p.Fiber U) (𝟭 (X.p.Fiber U))
    (Presheaf.restrictMap X AddCommGrpCat.{w} τ U) n

/-- Naturality of the fiberwise bar-homology coefficient map in the base category. -/
@[stacks 08PI "bar fiber homology coefficient map naturality"]
theorem map_naturality
    {F G : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}} (τ : F ⟶ G) (n : ℕ)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (presheaf X F n).map f ≫ mapApp X τ V.unop n =
      mapApp X τ U.unop n ≫ (presheaf X G n).map f := sorry

/-- The presheaf map on fiber bar homology induced by a total coefficient morphism. -/
@[stacks 08PI "bar fiber homology coefficient map"]
noncomputable abbrev map
    {F G : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}} (τ : F ⟶ G) (n : ℕ) :
    presheaf X F n ⟶ presheaf X G n where
  app U := mapApp X τ U.unop n
  naturality := fun {_ _} f ↦ map_naturality X τ n f

/-- The component of the bar fiber-homology coefficient map. -/
@[simp, stacks 08PI "bar fiber homology coefficient map component formula"]
theorem map_app
    {F G : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}} (τ : F ⟶ G) (n : ℕ) (U : Cᵒᵖ) :
    (map X τ n).app U = mapApp X τ U.unop n := sorry

/-- Fiber bar homology maps preserve identity coefficient morphisms. -/
@[simp, stacks 08PI "bar fiber homology coefficient identity"]
theorem map_id (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    map X (𝟙 F) n = 𝟙 (presheaf X F n) := sorry

/-- Fiber bar homology maps compose coefficient morphisms. -/
@[simp, stacks 08PI "bar fiber homology coefficient composition"]
theorem map_comp
    {F G H : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}} (τ : F ⟶ G) (σ : G ⟶ H) (n : ℕ) :
    map X (τ ≫ σ) n = map X τ n ≫ map X σ n := sorry

/-- Fiber bar homology as a functor from total coefficient presheaves to base presheaves. -/
@[stacks 08PI "bar fiber homology coefficient functor"]
noncomputable def presheafFunctor (n : ℕ) :
    (X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{w}) where
  obj F := presheaf X F n
  map τ := map X τ n
  map_id F := map_id X F n
  map_comp τ σ := map_comp X τ σ n

/-- The bar fiber-homology coefficient functor is additive. -/
@[stacks 08PI "additivity of bar fiber homology coefficient functor"]
instance presheafFunctor.additive (n : ℕ) : (presheafFunctor X n).Additive := sorry

/-- Evaluation of the bar fiber-homology coefficient functor on objects. -/
@[simp, stacks 08PI "bar fiber homology coefficient functor object formula"]
theorem presheafFunctor_obj (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    (presheafFunctor X n).obj F = presheaf X F n := sorry

/-- Evaluation of the bar fiber-homology coefficient functor on morphisms. -/
@[simp, stacks 08PI "bar fiber homology coefficient functor map formula"]
theorem presheafFunctor_map
    {F G : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}} (τ : F ⟶ G) (n : ℕ) :
    (presheafFunctor X n).map τ = map X τ n := sorry

variable [HasWeakSheafify J AddCommGrpCat.{w}]

/-- Fiber bar homology followed by sheafification, functorially in the total coefficients. -/
@[stacks 08PI "bar fiber homology sheaf coefficient functor"]
noncomputable abbrev sheafFunctor (n : ℕ) :
    (X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ Sheaf J AddCommGrpCat.{w} :=
  presheafFunctor X n ⋙ presheafToSheaf J AddCommGrpCat.{w}

/-- The sheaf-valued bar fiber-homology coefficient functor is additive. -/
@[stacks 08PI "additivity of bar fiber homology sheaf functor"]
instance sheafFunctor.additive (n : ℕ) : (sheafFunctor J X n).Additive := sorry

/-- The sheafification of the bar fiber-homology presheaf. -/
@[stacks 08PI "bar fiber category homology sheaf"]
abbrev sheaf
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    Sheaf J AddCommGrpCat.{w} :=
  (sheafFunctor J X n).obj F

/-- Evaluation of the sheaf-valued bar fiber-homology functor on objects. -/
@[simp, stacks 08PI "bar fiber homology sheaf functor object formula"]
theorem sheafFunctor_obj (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    (sheafFunctor J X n).obj F = sheaf J X F n := sorry

/-- The sheaf-level bar fiber-homology map induced by a total coefficient morphism. -/
@[stacks 08PI "bar fiber homology sheaf coefficient map"]
noncomputable abbrev sheafMap
    {F G : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}} (τ : F ⟶ G) (n : ℕ) :
    sheaf J X F n ⟶ sheaf J X G n :=
  (sheafFunctor J X n).map τ

/-- Evaluation of the sheaf-valued bar fiber-homology functor on morphisms. -/
@[simp, stacks 08PI "bar fiber homology sheaf functor map formula"]
theorem sheafFunctor_map
    {F G : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}} (τ : F ⟶ G) (n : ℕ) :
    (sheafFunctor J X n).map τ = sheafMap J X τ n := sorry

variable [HasWeakSheafify (X.p.inheritedTopology J) AddCommGrpCat.{w}]

/-- Fiber bar homology on sheaves of coefficients on the inherited total topology. -/
@[stacks 08PI "bar fiber homology functor on sheaves"]
noncomputable abbrev sheafOfSheafFunctor (n : ℕ) :
    Sheaf (X.p.inheritedTopology J) AddCommGrpCat.{w} ⥤ Sheaf J AddCommGrpCat.{w} :=
  sheafToPresheaf (X.p.inheritedTopology J) AddCommGrpCat.{w} ⋙ sheafFunctor J X n

/-- The bar fiber-homology functor on sheaves is additive. -/
@[stacks 08PI "additivity of bar fiber homology sheaf-of-sheaves functor"]
instance sheafOfSheafFunctor.additive (n : ℕ) :
    (sheafOfSheafFunctor J X n).Additive := sorry

/-- The bar fiber-homology sheaf attached to a sheaf on the inherited topology. -/
@[stacks 08PI "bar fiber homology sheaf of a sheaf"]
abbrev sheafOfSheaf
    (F : Sheaf (X.p.inheritedTopology J) AddCommGrpCat.{w}) (n : ℕ) :
    Sheaf J AddCommGrpCat.{w} :=
  (sheafOfSheafFunctor J X n).obj F

/-- Restriction of the sheafification unit to one fiber. -/
@[stacks 08PI "bar fiber restriction to the associated sheaf"]
abbrev restrictionToAssociated
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (V : C) :
    Presheaf.restrict X AddCommGrpCat.{w} F V ⟶
      Presheaf.restrict X AddCommGrpCat.{w}
        ((presheafToSheaf (X.p.inheritedTopology J) AddCommGrpCat.{w}).obj F).1 V :=
  Functor.whiskerLeft
    ((Functor.Fiber.fiberInclusion : X.p.Fiber V ⥤ X.total).op)
    (toSheafify (X.p.inheritedTopology J) F)

/-- The fiberwise bar-homology map induced by the sheafification unit. -/
@[stacks 08PI "bar fiber homology associated-sheaf component"]
abbrev associatedMapApp
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (V : Cᵒᵖ) (n : ℕ) :
    (presheaf X F n).obj V ⟶
      (presheaf X ((presheafToSheaf (X.p.inheritedTopology J)
        AddCommGrpCat.{w}).obj F).1 n).obj V :=
  mapApp X (toSheafify (X.p.inheritedTopology J) F) V.unop n

omit [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- Naturality of the bar-homology comparison induced by sheafification. -/
@[stacks 08PI "bar fiber homology associated-sheaf naturality"]
theorem associatedMap_naturality
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (presheaf X F n).map f ≫ associatedMapApp J X F V n =
      associatedMapApp J X F U n ≫
        (presheaf X ((presheafToSheaf (X.p.inheritedTopology J)
          AddCommGrpCat.{w}).obj F).1 n).map f := sorry

/-- The presheaf map on bar fiber homology induced by sheafification. -/
@[stacks 08PI "bar fiber homology associated-sheaf map"]
abbrev associatedMap
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    presheaf X F n ⟶
      presheaf X ((presheafToSheaf (X.p.inheritedTopology J)
        AddCommGrpCat.{w}).obj F).1 n :=
  map X (toSheafify (X.p.inheritedTopology J) F) n

/-- The associated-sheaf comparison on sheafified bar fiber homology. -/
@[stacks 08PI "bar fiber homology associated-sheaf morphism"]
abbrev sheafAssociatedHom
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    sheaf J X F n ⟶
      sheafOfSheaf J X
        ((presheafToSheaf (X.p.inheritedTopology J) AddCommGrpCat.{w}).obj F) n :=
  sheafMap J X (toSheafify (X.p.inheritedTopology J) F) n

/-- Sheafification does not change the sheafified bar fiber-homology presheaf. -/
@[stacks 08PI "bar fiber homology sheafification invariance"]
theorem sheafAssociatedHom_isIso
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    IsIso (sheafAssociatedHom J X F n) := sorry

/-- Canonical invertibility instance for the bar fiber-homology sheafification comparison. -/
instance sheafAssociatedHom.instIsIso
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    IsIso (sheafAssociatedHom J X F n) :=
  sorry

end CategoryTheory.FiberedCategoryOver.FiberHomology.Bar
