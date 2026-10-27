/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.FlatBaseChange.Properties
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GroupoidsOver

universe u v w

/- Lemma 103.7.2 (1): flat base change is preserved by arbitrary pullback
between algebraic stacks. -/
@[stacks 0764] #check
  (AlgebraicGeometry.GroupoidsOver.HasFlatBaseChange.pullback :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
      (g : Y ⟶ X) (F : etaleModules X) [HasFlatBaseChange F],
      HasFlatBaseChange ((etaleModuleInverseImage g).obj F))

/- Lemma 103.7.2 (2): all étale modules with flat base change form a weak
Serre subcategory. -/
@[stacks 0764] #check
  (AlgebraicGeometry.GroupoidsOver.HasFlatBaseChange.isWeakSerreClass :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
      (hasFlatBaseChange X).IsWeakSerreClass)

/- Lemma 103.7.2 (3): flat base change descends along a jointly point-covering
smooth family of algebraic stacks. -/
@[stacks 0764] #check
  (AlgebraicGeometry.GroupoidsOver.HasFlatBaseChange.ofSmoothCovering :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {ι : Type v}
      {Xi : ι → GroupoidsOver S} [∀ i, AlgebraicStack (Xi i)]
      (f : ∀ i, Xi i ⟶ X) [∀ i, AlgebraicStack.Smooth (f i)]
      (h_cover : ∀ x : AlgebraicStack.Points X,
        ∃ i, x ∈ Set.range (AlgebraicStack.Points.map (f i)))
      (F : etaleModules X)
      (hF : ∀ i, HasFlatBaseChange ((etaleModuleInverseImage (f i)).obj F)),
      HasFlatBaseChange F)

/- Lemma 103.7.2 (4): the full subcategory of étale modules with flat base
change admits all universe-compatible colimits; the inclusion creates them. -/
@[stacks 0764] #check
  (AlgebraicGeometry.GroupoidsOver.HasFlatBaseChange.hasColimitsOfShape :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      (J : Type v) [Category.{w} J] [HasColimitsOfShape J AddCommGrpCat.{u}],
      HasColimitsOfShape J (hasFlatBaseChange X).FullSubcategory)

#check
  (AlgebraicGeometry.GroupoidsOver.HasFlatBaseChange.closedUnderColimitsOfShape :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      (J : Type v) [Category.{w} J],
      (hasFlatBaseChange X).IsClosedUnderColimitsOfShape J)

section Colimits

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
  (J : Type v) [Category.{w} J] [HasColimitsOfShape J AddCommGrpCat.{u}]

#check
  (CategoryTheory.Limits.createsColimitsOfShapeFullSubcategoryInclusion
    J (hasFlatBaseChange X) : CreatesColimitsOfShape J (hasFlatBaseChange X).ι)

end Colimits

/- Lemma 103.7.2 (5): the tensor product of two modules with flat base change
again has flat base change. -/
@[stacks 0764] #check
  (AlgebraicGeometry.GroupoidsOver.HasFlatBaseChange.tensor :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      (F G : etaleModules X) [HasFlatBaseChange F] [HasFlatBaseChange G],
      HasFlatBaseChange (moduleTensorEtale F G))

/- Lemma 103.7.2 (6): sheaf Hom from a finitely presented module into a module
with flat base change again has flat base change. -/
@[stacks 0764] #check
  (AlgebraicGeometry.GroupoidsOver.HasFlatBaseChange.sheafHom :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      (F G : etaleModules X) [F.IsFinitePresentation] [HasFlatBaseChange G],
      HasFlatBaseChange (moduleSheafHomEtale F G))
