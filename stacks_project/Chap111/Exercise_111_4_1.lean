/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.EilenbergWatts.Counterexamples
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

/- Exercise 111.4.1 (1): restriction of scalars along `prodComm` is an additive functor
`ModuleCat (ℤ × ℤ) ⥤ ModuleCat (ℤ × ℤ)`. -/
@[stacks 0CYH] #check (ModuleCat.restrictScalars_prodComm_additive.{u} :
  ModuleCat.restrictScalars_prodComm.{u}.Additive)

/- Exercise 111.4.1 (2): restriction of scalars along `prodComm` is not `(ℤ × ℤ)`-linear. -/
@[stacks 0CYH] #check (ModuleCat.not_linear_restrictScalars_prodComm.{u} :
  ¬ ModuleCat.restrictScalars_prodComm.{u}.Linear (ℤ × ℤ))

/- Exercise 111.4.1 (3): the functor `M ↦ M ⊗ N` is `R`-linear. -/
@[stacks 0CYH] #check (ModuleCat.tensorRightLinear :
  ∀ {R : Type u} [CommRing R] (N : ModuleCat.{u} R), (tensorRight N).Linear R)

/- Exercise 111.4.1 (4): the functor `M ↦ M ⊗ N` is right exact. -/
@[stacks 0CYH] #check (ModuleCat.tensorRight_preservesFiniteColimits :
  ∀ {R : Type u} [CommRing R] (N : ModuleCat.{u} R),
    PreservesFiniteColimits (tensorRight N))

/- Exercise 111.4.1 (5): the functor `M ↦ M ⊗ N` commutes with direct sums. -/
@[stacks 0CYH] #check (ModuleCat.tensorRight_preservesColimitsOfShape_discrete :
  ∀ {R : Type u} [CommRing R] (N : ModuleCat.{u} R) (I : Type u),
    PreservesColimitsOfShape (Discrete I) (tensorRight N))

/- Exercise 111.4.1 (6): an `R`-linear right exact functor `F : ModuleCat R ⥤ ModuleCat R`
that commutes with direct sums is naturally isomorphic to `tensorRight (F.obj (of R R))`. -/
@[stacks 0CYH] #check (ModuleCat.isIso_tensorRightComparison :
  ∀ {R : Type u} [CommRing R] (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)
    [F.Additive] [F.Linear R] [PreservesFiniteColimits F]
    [∀ I : Type u, PreservesColimitsOfShape (Discrete I) F],
    IsIso (ModuleCat.tensorRightComparison F))

/- Exercise 111.4.1 (7): dropping preservation of direct sums, `F` need not be of the form
`tensorRight N`. -/
@[stacks 0CYH] #check (ModuleCat.not_isIso_tensorRightComparison_piConst :
  ∀ {R : Type u} [CommRing R] [Nontrivial R],
    ¬ IsIso (ModuleCat.tensorRightComparison (ModuleCat.piConst R (ULift.{u} ℕ))))

/- Exercise 111.4.1 (8): the countable product-power functor is not tensoring by any module. -/
@[stacks 0CYH] #check (ModuleCat.piConst_not_iso_tensorRight :
  ∀ {R : Type u} [CommRing R] [Nontrivial R] (N : ModuleCat.{u} R),
    ¬ Nonempty (ModuleCat.piConst R (ULift.{u} ℕ) ≅ tensorRight N))
