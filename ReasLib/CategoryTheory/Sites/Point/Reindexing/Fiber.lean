module

public import Mathlib.CategoryTheory.Limits.FinallySmall
public import Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered
public import ReasLib.CategoryTheory.Sites.Point.Reindexing.Comparison

/-!
# Fiber maps for reindexed inverse systems

An arbitrary reindexing functor equipped with an identification of inverse
systems induces a natural transformation between their object fibers.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v q w₀ w₁ w₂ v₀ v₁ v₂

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

variable {C : Type u} [Category.{v} C]

namespace Reindexing

variable {I : Type w₀} [Category.{v₀} I]
variable {I' : Type w₁} [Category.{v₁} I']
variable [LocallySmall.{q} C]
variable [InitiallySmall.{q} Iᵒᵖ] [InitiallySmall.{q} I'ᵒᵖ]
variable {S : Iᵒᵖ ⥤ C}

/-- Internal colimit availability for the source fiber diagram, derived canonically from
the source smallness assumption. -/
local instance sourceHasColimitsOfShape : HasColimitsOfShape Iᵒᵖᵒᵖ (Type q) :=
  hasColimitsOfShape_of_finallySmall _ _

/-- Internal colimit availability for the target fiber diagram, derived canonically from
the target smallness assumption. -/
local instance targetHasColimitsOfShape : HasColimitsOfShape I'ᵒᵖᵒᵖ (Type q) :=
  hasColimitsOfShape_of_finallySmall _ _

/-- The diagram of `Type q` whose colimit computes the inverse-system fiber of `S` at `W`. -/
noncomputable abbrev fiberDiagram (S : Iᵒᵖ ⥤ C) (W : C) :
    Iᵒᵖᵒᵖ ⥤ Type q :=
  S.op ⋙ shrinkYoneda.{q}.obj W

/-- The functor between colimit index categories induced by a reindexing functor. -/
noncomputable abbrev indexFunctor (j : I ⥤ I') :
    Iᵒᵖᵒᵖ ⥤ I'ᵒᵖᵒᵖ :=
  j.op.op

/-- The comparison of fiber diagrams supplied by a reindexing isomorphism. -/
noncomputable abbrev diagramHom
    (j : I ⥤ I') (T : I'ᵒᵖ ⥤ C) (e : S ≅ j.op ⋙ T) :
    S.op ⟶ indexFunctor j ⋙ T.op :=
  NatTrans.op e.inv ≫ (Functor.opComp j.op T).hom

/-- The map between the diagrams computing the source and target fibers of a reindexing. -/
noncomputable def diagramMap
    (j : I ⥤ I') (T : I'ᵒᵖ ⥤ C) (e : S ≅ j.op ⋙ T) (W : C) :
    fiberDiagram S W ⟶ indexFunctor j ⋙ fiberDiagram T W :=
  Functor.whiskerRight (diagramHom j T e) (shrinkYoneda.{q}.obj W)

/-- The objectwise map on inverse-system fibers induced by reindexing. -/
noncomputable def fiberApp
    (j : I ⥤ I') (T : I'ᵒᵖ ⥤ C) (e : S ≅ j.op ⋙ T) (W : C) :
    (fiber.{q} S).obj W ⟶ (fiber.{q} T).obj W :=
  colim.map (diagramMap j T e W) ≫
    colimit.pre (fiberDiagram T W) (indexFunctor j)

/-- The objectwise reindexing map sends a canonical fiber generator to its transported
generator. -/
theorem fiberApp_fiberMk
    (j : I ⥤ I') (T : I'ᵒᵖ ⥤ C) (e : S ≅ j.op ⋙ T)
    {U : Iᵒᵖ} {W : C} (f : S.obj U ⟶ W) :
    fiberApp j T e W (fiberMk.{q} f) =
      fiberMk.{q} (p := T) (e.inv.app U ≫ f) := sorry

/-- The objectwise reindexing maps are natural in the object of `C`. -/
theorem fiberApp_naturality
    (j : I ⥤ I') (T : I'ᵒᵖ ⥤ C) (e : S ≅ j.op ⋙ T)
    {X Y : C} (f : X ⟶ Y) :
    (fiber.{q} S).map f ≫ fiberApp j T e Y =
      fiberApp j T e X ≫ (fiber.{q} T).map f := sorry

/-- The natural transformation on inverse-system fibers induced by a reindexing
`S ≅ j.op ⋙ T`. -/
noncomputable def fiber
    (j : I ⥤ I') (T : I'ᵒᵖ ⥤ C) (e : S ≅ j.op ⋙ T) :
    fiber.{q} S ⟶ fiber.{q} T where
  app := fiberApp j T e
  naturality _ _ f := fiberApp_naturality j T e f

/-- Evaluating the reindexing fiber map on a canonical generator transports that generator
along the given inverse-system isomorphism. -/
@[simp]
theorem fiber_app_fiberMk
    (j : I ⥤ I') (T : I'ᵒᵖ ⥤ C) (e : S ≅ j.op ⋙ T)
    {U : Iᵒᵖ} {W : C} (f : S.obj U ⟶ W) :
    (fiber j T e).app W (fiberMk.{q} f) =
      fiberMk.{q} (p := T) (e.inv.app U ≫ f) := sorry

/-- Reindexing an inverse system along the identity functor induces the identity fiber map. -/
@[simp]
theorem fiber_id (S : Iᵒᵖ ⥤ C) :
    fiber (𝟭 I) S (idIso S) =
      𝟙 (CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.fiber.{q} S) := sorry

section Composition

variable {I'' : Type w₂} [Category.{v₂} I'']
variable [InitiallySmall.{q} I''ᵒᵖ]
variable {T : I'ᵒᵖ ⥤ C} {U : I''ᵒᵖ ⥤ C}

/-- Internal colimit availability for the final fiber diagram in a composite reindexing. -/
local instance finalHasColimitsOfShape : HasColimitsOfShape I''ᵒᵖᵒᵖ (Type q) :=
  hasColimitsOfShape_of_finallySmall _ _

/-- Fiber maps of successive reindexings compose to the fiber map of their composite. -/
@[simp]
theorem fiber_comp
    (j : I ⥤ I') (k : I' ⥤ I'') (e : S ≅ j.op ⋙ T) (e' : T ≅ k.op ⋙ U) :
    fiber (j ⋙ k) U (compIso j k e e') = fiber j T e ≫ fiber k U e' := sorry

end Composition

end Reindexing

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
