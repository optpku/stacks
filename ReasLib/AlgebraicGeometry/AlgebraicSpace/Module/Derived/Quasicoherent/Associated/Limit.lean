/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Associated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-! # Sequential limits of associated modules on algebraic spaces -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.Associated

variable {R : Type u} [CommRing R]
variable {X : AlgebraicSpace (Spec (CommRingCat.of R))}

/-- The degree-zero image of the canonical map from the associated module of an inverse
limit to the inverse limit of the associated modules. -/
noncomputable def limitComparison
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (M : SequentialInverseSystem (ModuleCat.{u} R)) :
    (single f (limit M)).obj ⟶
      (DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).obj
        (limit (M ⋙ associatedFunctor f)) :=
  (DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).map
    (limit.post M (associatedFunctor f))

/-- Composing the associated-module limit comparison with a degree-zero limit projection
recovers the degree-zero image of the corresponding module-limit projection. -/
theorem limitComparison_π
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (M : SequentialInverseSystem (ModuleCat.{u} R)) (n : ℕ) :
    limitComparison f M ≫
        (DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).map
          (limit.π (M ⋙ associatedFunctor f) (Opposite.op n)) =
      (DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).map
        ((associatedFunctor f).map (limit.π M (Opposite.op n))) := by
  exact ((DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).map_comp
    (limit.post M (associatedFunctor f))
    (limit.π (M ⋙ associatedFunctor f) (Opposite.op n))).symm.trans
      (congrArg ((DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).map)
        (limit.post_π M (associatedFunctor f) (Opposite.op n)))

/-- For a proper, flat morphism of finite presentation to an affine scheme and a sequential
inverse system of modules with epimorphic transitions, the canonical associated-module limit
comparison induces a bijection on morphisms from every derived quasi-coherent object. -/
theorem limitComparison_hom_bijective
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    [Proper f] [Flat f] [FinitePresentation f]
    (M : SequentialInverseSystem (ModuleCat.{u} R))
    [∀ n : ℕ, Epi (SequentialInverseSystem.transitionMap M (Nat.le_succ n))]
    (E : DerivedQCoh X) :
    Function.Bijective
      (fun g : E.obj ⟶ (single f (limit M)).obj => g ≫ limitComparison f M) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.Associated
