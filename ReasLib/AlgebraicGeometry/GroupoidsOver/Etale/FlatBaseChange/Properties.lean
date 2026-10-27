/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.FlatBaseChange
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.InternalHom
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.LocallyQuasiCoherent
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre

/-!
# Closure properties of flat base change

Étale modules with flat base change form a weak Serre class, have colimits,
and are stable under pullback, smooth descent, tensor products, and internal Hom
from finitely presented modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace AlgebraicGeometry.GroupoidsOver.HasFlatBaseChange

variable {S : Scheme.{u}}

/-- Pullback along a morphism of algebraic stacks preserves flat base change. -/
instance pullback {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (g : Y ⟶ X) (F : etaleModules X) [HasFlatBaseChange F] :
    HasFlatBaseChange ((etaleModuleInverseImage g).obj F) := sorry

/-- Étale modules with flat base change form a weak Serre class. -/
instance isWeakSerreClass (X : GroupoidsOver S) [AlgebraicStack X] :
    (hasFlatBaseChange X).IsWeakSerreClass := sorry

/-- Flat base change descends along a jointly point-covering smooth family of algebraic stacks. -/
theorem ofSmoothCovering {X : GroupoidsOver S} [AlgebraicStack X] {ι : Type v}
    {Xi : ι → GroupoidsOver S} [∀ i, AlgebraicStack (Xi i)]
    (f : ∀ i, Xi i ⟶ X) [∀ i, AlgebraicStack.Smooth (f i)]
    (h_cover : ∀ x : AlgebraicStack.Points X,
      ∃ i, x ∈ Set.range (AlgebraicStack.Points.map (f i)))
    (F : etaleModules X)
    (hF : ∀ i, HasFlatBaseChange ((etaleModuleInverseImage (f i)).obj F)) :
    HasFlatBaseChange F := sorry

/-- Flat base change is stable under colimits computed in the ambient étale module category. -/
instance closedUnderColimitsOfShape (X : GroupoidsOver S) [AlgebraicStack X]
    (J : Type v) [Category.{w} J] :
    (hasFlatBaseChange X).IsClosedUnderColimitsOfShape J := sorry

/-- Étale modules with flat base change have colimits of every universe-compatible shape. -/
instance hasColimitsOfShape (X : GroupoidsOver S) [AlgebraicStack X]
    (J : Type v) [Category.{w} J] [HasColimitsOfShape J AddCommGrpCat.{u}] :
    HasColimitsOfShape J (hasFlatBaseChange X).FullSubcategory :=
  hasColimitsOfShape_of_closedUnderColimits J (hasFlatBaseChange X)

/-- The tensor product of two étale modules with flat base change has flat base change. -/
instance tensor {X : GroupoidsOver S} [AlgebraicStack X]
    (F G : etaleModules X) [HasFlatBaseChange F] [HasFlatBaseChange G] :
    HasFlatBaseChange (moduleTensorEtale F G) := sorry

/-- Internal Hom from a finitely presented étale module into a module with flat base change
has flat base change. -/
instance sheafHom {X : GroupoidsOver S} [AlgebraicStack X]
    (F G : etaleModules X) [F.IsFinitePresentation] [HasFlatBaseChange G] :
    HasFlatBaseChange (moduleSheafHomEtale F G) := sorry

end AlgebraicGeometry.GroupoidsOver.HasFlatBaseChange
