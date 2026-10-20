/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.CategoryTheory.Category.Cat.Op
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import ReasLib.CategoryTheory.Sites.PrecoverageSite

/-! Total categories and selected site structures for simplicial diagrams of sites. -/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace CategoryTheory.SimplicialSites

/-- The opposite Grothendieck category associated to a simplicial diagram of categories. -/
abbrev totalSite (C : SimplexCategory ⥤ Cat.{v, u}) : Type u :=
  (Grothendieck (C ⋙ Cat.opFunctor.{v, u}))ᵒᵖ

/-- The total-category object represented by an object of a specified stage. -/
def ofObj (C : SimplexCategory ⥤ Cat.{v, u}) (n : SimplexCategory) (U : C.obj n) :
    totalSite C :=
  op ⟨n, op U⟩

/-- The simplex degree of an object in the total category. -/
def degree {C : SimplexCategory ⥤ Cat.{v, u}} (U : totalSite C) : SimplexCategory :=
  U.unop.base

/-- The stage object underlying an object in the total category. -/
def obj {C : SimplexCategory ⥤ Cat.{v, u}} (U : totalSite C) : C.obj (degree U) :=
  U.unop.fiber.unop

/-- The degree of an object represented by `ofObj` is its specified stage. -/
theorem ofObj_degree (C : SimplexCategory ⥤ Cat.{v, u}) (n : SimplexCategory) (U : C.obj n) :
    degree (ofObj C n U) = n := sorry

/-- The stage object represented by `ofObj` is its specified object. -/
theorem ofObj_obj (C : SimplexCategory ⥤ Cat.{v, u}) (n : SimplexCategory) (U : C.obj n) :
    obj (ofObj C n U) = U := sorry

/-- Every total-category object is represented by its degree and stage object. -/
theorem eq_ofObj {C : SimplexCategory ⥤ Cat.{v, u}} (U : totalSite C) :
    U = ofObj C (degree U) (obj U) := sorry

/-- A total-category morphism from a simplex operator and a stage morphism. -/
def homMk {C : SimplexCategory ⥤ Cat.{v, u}} {U V : totalSite C}
    (φ : degree V ⟶ degree U) (f : obj U ⟶ (C.map φ).toFunctor.obj (obj V)) : U ⟶ V :=
  op ({ base := φ, fiber := op f } : V.unop ⟶ U.unop)

/-- The stage functor associated to a composite simplex operator. -/
theorem map_comp_toFunctor_obj (C : SimplexCategory ⥤ Cat.{v, u})
    {k m n : SimplexCategory} (ψ : k ⟶ m) (φ : m ⟶ n) (W : C.obj k) :
    (C.map φ).toFunctor.obj ((C.map ψ).toFunctor.obj W) =
      (C.map (ψ ≫ φ)).toFunctor.obj W := sorry

/-- Composition of total-category morphisms in stage coordinates. -/
theorem homMk_comp {C : SimplexCategory ⥤ Cat.{v, u}} {U V W : totalSite C}
    (φ : degree V ⟶ degree U) (f : obj U ⟶ (C.map φ).toFunctor.obj (obj V))
    (ψ : degree W ⟶ degree V) (g : obj V ⟶ (C.map ψ).toFunctor.obj (obj W)) :
    homMk φ f ≫ homMk ψ g =
      homMk (ψ ≫ φ)
        (f ≫ (C.map φ).toFunctor.map g ≫ eqToHom (map_comp_toFunctor_obj C ψ φ (obj W))) := sorry

/-- The simplex operator and stage morphism underlying a total-category morphism. -/
def homToPair {C : SimplexCategory ⥤ Cat.{v, u}} {U V : totalSite C} (f : U ⟶ V) :
    Σ φ : degree V ⟶ degree U, obj U ⟶ (C.map φ).toFunctor.obj (obj V) :=
  ⟨f.unop.base, f.unop.fiber.unop⟩

/-- Reconstructing a total-category morphism from its coordinate pair returns that morphism. -/
theorem homMk_homToPair {C : SimplexCategory ⥤ Cat.{v, u}} {U V : totalSite C} (f : U ⟶ V) :
    homMk (homToPair f).1 (homToPair f).2 = f := sorry

/-- Reading the coordinates of a constructed total-category morphism returns the specified pair. -/
theorem homToPair_homMk {C : SimplexCategory ⥤ Cat.{v, u}} {U V : totalSite C}
    (φ : degree V ⟶ degree U) (f : obj U ⟶ (C.map φ).toFunctor.obj (obj V)) :
    homToPair (homMk φ f) = ⟨φ, f⟩ := sorry

/-- The equivalence between total-category morphisms and stage-coordinate pairs. -/
def homEquiv {C : SimplexCategory ⥤ Cat.{v, u}} {U V : totalSite C} :
    (U ⟶ V) ≃ Σ φ : degree V ⟶ degree U, obj U ⟶ (C.map φ).toFunctor.obj (obj V) where
  toFun := homToPair
  invFun p := homMk p.1 p.2
  left_inv := homMk_homToPair
  right_inv p := homToPair_homMk p.1 p.2

/-- Evaluation of `homEquiv` returns the coordinate pair of a morphism. -/
theorem homEquiv_apply {C : SimplexCategory ⥤ Cat.{v, u}} {U V : totalSite C} (f : U ⟶ V) :
    homEquiv f = homToPair f := sorry

/-- Evaluation of the inverse of `homEquiv` constructs the specified morphism. -/
theorem homEquiv_symm_apply {C : SimplexCategory ⥤ Cat.{v, u}} {U V : totalSite C}
    (φ : degree V ⟶ degree U) (f : obj U ⟶ (C.map φ).toFunctor.obj (obj V)) :
    homEquiv.symm ⟨φ, f⟩ = homMk φ f := sorry

/-- A stage morphism defines a total-category morphism with identity simplex operator. -/
def ofStageMap (C : SimplexCategory ⥤ Cat.{v, u}) (n : SimplexCategory)
    {X Y : C.obj n} (f : X ⟶ Y) : ofObj C n X ⟶ ofObj C n Y :=
  homMk (𝟙 n)
    (f ≫ eqToHom ((congrArg (fun G : C.obj n ⟶ C.obj n ↦ G.toFunctor.obj Y)
      (C.map_id n)).trans (Cat.Hom.id_obj Y)).symm)

/-- The identity-simplex lift of a stage identity is a total-category identity. -/
theorem ofStageMap_id (C : SimplexCategory ⥤ Cat.{v, u}) (n : SimplexCategory) (X : C.obj n) :
    ofStageMap C n (𝟙 X) = 𝟙 (ofObj C n X) := sorry

/-- The identity-simplex lift preserves composition of stage morphisms. -/
theorem ofStageMap_comp (C : SimplexCategory ⥤ Cat.{v, u}) (n : SimplexCategory)
    {X Y Z : C.obj n} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ofStageMap C n (f ≫ g) = ofStageMap C n f ≫ ofStageMap C n g := sorry

/-- The identity-simplex inclusion of a stage into the total category. -/
def ofStage (C : SimplexCategory ⥤ Cat.{v, u}) (n : SimplexCategory) :
    C.obj n ⥤ totalSite C where
  obj U := ofObj C n U
  map := ofStageMap C n
  map_id := ofStageMap_id C n
  map_comp := ofStageMap_comp C n

/-- The object map of `ofStage` is the canonical stage-object inclusion. -/
theorem ofStage_obj (C : SimplexCategory ⥤ Cat.{v, u}) (n : SimplexCategory) (U : C.obj n) :
    (ofStage C n).obj U = ofObj C n U := sorry

/-- The arrow map of the stage inclusion is the identity-simplex lift. -/
theorem ofStage_map (C : SimplexCategory ⥤ Cat.{v, u}) (n : SimplexCategory)
    {X Y : C.obj n} (f : X ⟶ Y) :
    (ofStage C n).map f = ofStageMap C n f := sorry

/-- The identity-simplex presieve associated to a family of stage morphisms. -/
def ofStageArrows {C : SimplexCategory ⥤ Cat.{v, u}} {U : totalSite C}
    {ι : Type (max u v)} (X : ι → C.obj (degree U)) (f : ∀ i, X i ⟶ obj U) : Presieve U :=
  Presieve.ofArrows (fun i ↦ (ofStage C (degree U)).obj (X i))
    (fun i ↦ (ofStage C (degree U)).map (f i))

/-- A simplicial diagram with site precoverages and continuous structure functors. -/
class IsSiteDiagram (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n)) : Prop where
  /-- Each stage precoverage satisfies the site axioms. -/
  isSite : ∀ n, (J n).IsSite
  /-- Each structure functor preserves the selected precoverage structure. -/
  isContinuous : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    Functor.Precoverage.IsContinuous (C.map φ).toFunctor (J m) (J n)

/-- The defining stagewise and continuity conditions for a simplicial site diagram. -/
theorem IsSiteDiagram.iff (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n)) :
    IsSiteDiagram C J ↔
      (∀ n, (J n).IsSite) ∧
        ∀ {m n : SimplexCategory} (φ : m ⟶ n),
          Functor.Precoverage.IsContinuous (C.map φ).toFunctor (J m) (J n) := sorry

/-- A constant diagram of a site satisfies the simplicial site-diagram conditions. -/
instance IsSiteDiagram.const {C : Type u} [Category.{v} C] (J : Precoverage C) [J.IsSite] :
    IsSiteDiagram ((Functor.const SimplexCategory).obj (Cat.of C)) (fun _ ↦ J) := sorry

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))

/-- The precoverage of identity-simplex lifts of stage covering families. -/
def precoverage : Precoverage (totalSite C) where
  coverings U :=
    {R | ∃ (ι : Type (max u v)) (X : ι → C.obj (degree U)) (f : ∀ i, X i ⟶ obj U),
      R = ofStageArrows X f ∧ Presieve.ofArrows X f ∈ J (degree U) (obj U)}

/-- Membership in the total precoverage is characterized by a stage covering family. -/
theorem mem_precoverage_iff {U : totalSite C} {R : Presieve U} :
    R ∈ precoverage C J U ↔
      ∃ (ι : Type (max u v)) (X : ι → C.obj (degree U)) (f : ∀ i, X i ⟶ obj U),
        R = ofStageArrows X f ∧ Presieve.ofArrows X f ∈ J (degree U) (obj U) := sorry

/-- An identity-simplex family is covering exactly when its stage family is covering. -/
theorem ofStageArrows_mem_iff {U : totalSite C} {ι : Type (max u v)}
    (X : ι → C.obj (degree U)) (f : ∀ i, X i ⟶ obj U) :
    ofStageArrows X f ∈ precoverage C J U ↔
      Presieve.ofArrows X f ∈ J (degree U) (obj U) := sorry

/-- The total precoverage contains singleton isomorphism families. -/
instance precoverage.hasIsos [IsSiteDiagram C J] : (precoverage C J).HasIsos := sorry

/-- The total precoverage is stable under composition of covering families. -/
instance precoverage.isStableUnderBind [IsSiteDiagram C J] :
    (precoverage C J).IsStableUnderBind := sorry

/-- Covering arrows in the total precoverage admit pullback families. -/
instance precoverage.hasPullbacks [IsSiteDiagram C J] : (precoverage C J).HasPullbacks := sorry

/-- Covering pullback families factor through their original covering families. -/
instance precoverage.hasFactoringPullbacks [IsSiteDiagram C J] :
    (precoverage C J).HasFactoringPullbacks := sorry

/-- Pullback families of total covering arrows are again selected covers. -/
instance precoverage.isStableUnderPullbackArrows [IsSiteDiagram C J] :
    (precoverage C J).IsStableUnderPullbackArrows := sorry

/-- The identity-simplex precoverage of a simplicial site diagram is a site. -/
instance precoverage.isSite [IsSiteDiagram C J] : (precoverage C J).IsSite := sorry

/-- Stage fibre products give pullback squares for base changes of selected covers. -/
theorem exists_ofStage_isPullback [IsSiteDiagram C J] {U W : totalSite C} (g : W ⟶ U)
    {ι : Type (max u v)} (X : ι → C.obj (degree U)) (f : ∀ i, X i ⟶ obj U)
    (hf : Presieve.ofArrows X f ∈ J (degree U) (obj U)) :
    ∃ (P : ι → C.obj (degree W)) (p : ∀ i, P i ⟶ obj W)
      (q : ∀ i, P i ⟶ (C.map g.unop.base).toFunctor.obj (X i)),
      ofStageArrows P p ∈ precoverage C J W ∧
        ∀ i, IsPullback ((ofStage C (degree W)).map (p i))
          (homMk g.unop.base (q i) :
            (ofStage C (degree W)).obj (P i) ⟶ (ofStage C (degree U)).obj (X i))
          g ((ofStage C (degree U)).map (f i)) := sorry

/-- The Grothendieck topology generated by the total precoverage. -/
def topology : GrothendieckTopology (totalSite C) :=
  (precoverage C J).toGrothendieck

end CategoryTheory.SimplicialSites
