/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Construction.Unit
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Construction.HomDescent
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck

/-!
# Realizing the stackification stages over the original base

The supplied cleavage determines the local-arrow cleavage. The completed fibre
pseudofunctor is realized by the native co-Grothendieck category. Its comparison
uses the original Cartesian factor and the explicit unit restriction comparison.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory

noncomputable section

universe u v uX vX

namespace CategoryTheory.Functor.StackificationConstruction

variable {C : Type u} [Category.{v} C] {X : Type uX} [Category.{vX} X]
variable (J : GrothendieckTopology C) (p : X ⥤ C) (χ : p.Cleavage)

/-- The local-arrow cleavage keeps the original chosen lift objects and maps. -/
def localCleavage : (Localized.projection J p χ).Cleavage where
  lift {a V} f :=
    let l := χ.lift (x := a.obj.obj) f
    { source := (Localized.fromOriginal J p χ).obj l.source
      hom := (Localized.fromOriginal J p χ).map l.hom
      isStronglyCartesian :=
        @Localized.mapIsStronglyCartesian _ _ _ _ J p χ _ _ _ _ f l.hom l.isStronglyCartesian }

/-- The actual fibres and restrictions of the local-arrow stage. -/
def localFibers : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{max u v vX, uX} :=
  (localCleavage J p χ).toPseudofunctor

/-- The actual strict presheaf of completed descent objects. -/
def completedPresheaf : Cᵒᵖ ⥤ Cat.{max u v vX, max u v uX vX} :=
  DescentCompletion.presheaf J (localFibers J p χ)

/-- The target projection is the native realization of those actual fibres. -/
def targetProjection :
    Pseudofunctor.CoGrothendieck (completedPresheaf J p χ).toPseudofunctor' ⥤ C :=
  Pseudofunctor.CoGrothendieck.forget (completedPresheaf J p χ).toPseudofunctor'

/-- An original local-arrow object is viewed in the fibre over its actual base. -/
def localFiberObject (a : Localized J p χ) :
    (Localized.projection J p χ).Fiber ((Localized.projection J p χ).obj a) :=
  ⟨a, rfl⟩

/-- The original local-arrow stage maps into the actual realized completion. -/
def realizationFunctor : Localized J p χ ⥤
    Pseudofunctor.CoGrothendieck (completedPresheaf J p χ).toPseudofunctor' where
  obj a :=
    ⟨(Localized.projection J p χ).obj a,
      DescentCompletion.ofObject J (localFibers J p χ) (localFiberObject J p χ a)⟩
  map {a b} τ :=
    { base := (Localized.projection J p χ).map τ
      fiber :=
        (DescentCompletion.unitFunctor J (localFibers J p χ)
          ((Localized.projection J p χ).obj a)).map ((localCleavage J p χ).verticalFactor τ) ≫
          (DescentCompletion.unitReindexIso J (localFibers J p χ)
            ((Localized.projection J p χ).map τ) (localFiberObject J p χ b)).hom }
  map_id := sorry
  map_comp := sorry

/-- Realization is literally over the original base. -/
theorem realizationFunctor_comp_projection :
    realizationFunctor J p χ ⋙ targetProjection J p χ = Localized.projection J p χ := by
  rfl

/-- The realized comparison retains the underlying functor and its exact base map. -/
def realizationBased :
    BasedCategory.ofFunctor (Localized.projection J p χ) ⥤ᵇ
      BasedCategory.ofFunctor (targetProjection J p χ) :=
  BasedFunctor.ofFunctor (realizationFunctor J p χ) (realizationFunctor_comp_projection J p χ)

end CategoryTheory.Functor.StackificationConstruction
