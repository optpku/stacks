module

public import ReasLib.CategoryTheory.Sites.Point.EssentiallySmallFiber.Basic
public import ReasLib.CategoryTheory.Sites.Point.Reindexing.Fiber

/-!
# Fiber reindexing for essentially-small inverse systems

This is the ergonomic reindexing interface which derives the implementation
`InitiallySmall` instances from essential smallness.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v q w₀ w₁ w₂ v₀ v₁ v₂

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.Reindexing

namespace EssentiallySmall

variable {C : Type u} [Category.{v} C]
variable {I : Type w₀} [Category.{v₀} I]
variable {I' : Type w₁} [Category.{v₁} I']
variable {S : Iᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} Iᵒᵖ] [EssentiallySmall.{q} I'ᵒᵖ]

/-- Internal smallness bridge used by the essentially-small reindexing interface. -/
local instance sourceInitiallySmallOfEssentiallySmall : InitiallySmall.{q} Iᵒᵖ :=
  initiallySmall_of_essentiallySmall Iᵒᵖ

/-- Internal smallness bridge used by the essentially-small reindexing interface. -/
local instance targetInitiallySmallOfEssentiallySmall : InitiallySmall.{q} I'ᵒᵖ :=
  initiallySmall_of_essentiallySmall I'ᵒᵖ

/-- The reindexing map on inverse-system fibers when both indexing categories are essentially
small in the fiber universe.  This is the ergonomic interface for ordinary small index types;
it internalizes the conversion from essential smallness to the initial-smallness hypotheses of
`fiber`. -/
noncomputable def fiber
    (j : I ⥤ I') (T : I'ᵒᵖ ⥤ C) (e : S ≅ j.op ⋙ T) :
    EssentiallySmallFiber.fiber S ⟶ EssentiallySmallFiber.fiber T :=
  CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.Reindexing.fiber.{u, v, q, w₀, w₁, v₀, v₁}
    j T e

/-- The essentially-small reindexing map has the same formula on canonical fiber generators. -/
@[simp]
theorem fiber_app_fiberMk
    (j : I ⥤ I') (T : I'ᵒᵖ ⥤ C) (e : S ≅ j.op ⋙ T)
    {U : Iᵒᵖ} {W : C} (f : S.obj U ⟶ W) :
    (fiber j T e).app W (fiberMk.{q} f) =
      fiberMk.{q} (p := T) (e.inv.app U ≫ f) := sorry

/-- Essentially-small reindexing sends a public canonical generator to the
canonical generator obtained by precomposing with the comparison isomorphism. -/
@[simp]
theorem fiber.app.mk
    (j : I ⥤ I') (T : I'ᵒᵖ ⥤ C) (e : S ≅ j.op ⋙ T)
    {U : Iᵒᵖ} {W : C} (f : S.obj U ⟶ W) :
    (fiber j T e).app W (EssentiallySmallFiber.mk (S := S) f) =
      EssentiallySmallFiber.mk (S := T) (e.inv.app U ≫ f) := sorry

/-- Identity reindexing acts as the identity through the essentially-small fiber interface. -/
@[simp]
theorem fiber_id (S : Iᵒᵖ ⥤ C) :
    fiber (𝟭 I) S (idIso S) = 𝟙 (EssentiallySmallFiber.fiber S) := sorry

section Composition

variable {I'' : Type w₂} [Category.{v₂} I'']
variable [EssentiallySmall.{q} I''ᵒᵖ]
variable {T : I'ᵒᵖ ⥤ C} {U : I''ᵒᵖ ⥤ C}

/-- Internal smallness bridge for the final index category of an essentially-small composite. -/
local instance finalInitiallySmallOfEssentiallySmall : InitiallySmall.{q} I''ᵒᵖ :=
  initiallySmall_of_essentiallySmall I''ᵒᵖ

/-- Successive essentially-small reindexings induce the fiber map of their composite. -/
@[simp]
theorem fiber_comp
    (j : I ⥤ I') (k : I' ⥤ I'') (e : S ≅ j.op ⋙ T) (e' : T ≅ k.op ⋙ U) :
    fiber (j ⋙ k) U (compIso j k e e') =
      fiber j T e ≫ fiber k U e' := sorry

end Composition

end EssentiallySmall

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.Reindexing
