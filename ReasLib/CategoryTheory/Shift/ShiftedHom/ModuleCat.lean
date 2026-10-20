module

public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.CategoryTheory.Linear.Opposite
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Equiv
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Shifted morphisms as module-valued functors

In an `R`-linear category with shifts, shifted morphisms are naturally `R`-modules.  This file
packages their covariance in the target and contravariance in the source without choosing
elements or rebuilding composition maps at each use site.
-/

@[expose] public section

universe uR uS v u

open CategoryTheory Opposite

namespace CategoryTheory.ShiftedHom

variable (R : Type uR) [Ring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C] [HasShift C ℤ]

/-- Moving a shift from the target to the source is an `R`-linear equivalence.  Both functions
are the canonical source-shift equivalence, so no inverse is selected from bijectivity. -/
@[stacks 0G1X "linear source-shift equivalence for shifted Hom"]
noncomputable def sourceShiftLinearEquiv (X Y : C) (n : ℤ)
    [(shiftFunctor C (-n)).Additive] [Functor.Linear R (shiftFunctor C (-n))] :
    ShiftedHom X Y n ≃ₗ[R] (X⟦-n⟧ ⟶ Y) where
  toFun := ShiftedHom.sourceShiftEquiv X Y n
  invFun := (ShiftedHom.sourceShiftEquiv X Y n).symm
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry
  map_smul' := sorry

/-- Degree-zero shifted morphisms are linearly equivalent to ordinary morphisms. -/
@[stacks 0G1X "degree-zero shifted Hom linear equivalence"]
noncomputable def zeroLinearEquiv (X Y : C) :
    ShiftedHom X Y (0 : ℤ) ≃ₗ[R] (X ⟶ Y) where
  toFun := (ShiftedHom.homEquiv (0 : ℤ) rfl).symm
  invFun := ShiftedHom.homEquiv (0 : ℤ) rfl
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry
  map_smul' := sorry

/-- The forward map of `zeroLinearEquiv` is the inverse of the canonical zero-degree Hom
equivalence. -/
@[simp, stacks 0G1X "degree-zero shifted Hom linear equivalence forward map"]
theorem zeroLinearEquiv_apply (X Y : C) (f : ShiftedHom X Y (0 : ℤ)) :
    zeroLinearEquiv R X Y f = (ShiftedHom.homEquiv (0 : ℤ) rfl).symm f := sorry

/-- The forward function of `sourceShiftLinearEquiv` is the canonical source-shift map. -/
@[simp]
theorem sourceShiftLinearEquiv_apply (X Y : C) (n : ℤ)
    [(shiftFunctor C (-n)).Additive] [Functor.Linear R (shiftFunctor C (-n))]
    (f : ShiftedHom X Y n) :
    sourceShiftLinearEquiv R X Y n f = ShiftedHom.sourceShiftEquiv X Y n f := sorry

/-- The inverse function of `sourceShiftLinearEquiv` is the inverse canonical source-shift
map. -/
@[simp]
theorem sourceShiftLinearEquiv_symm_apply
    (X Y : C) (n : ℤ)
    [(shiftFunctor C (-n)).Additive] [Functor.Linear R (shiftFunctor C (-n))]
    (f : X⟦-n⟧ ⟶ Y) :
    (sourceShiftLinearEquiv R X Y n).symm f =
      (ShiftedHom.sourceShiftEquiv X Y n).symm f := sorry

/-- Shifted morphisms as a module-valued functor, contravariant in the source and covariant in
the target. -/
@[stacks 0G1X "linear shifted Hom bifunctor"]
def linearCoyoneda (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C]
    [HasShift C ℤ] (n : ℤ) : Cᵒᵖ ⥤ C ⥤ ModuleCat.{v} R :=
  CategoryTheory.linearCoyoneda R C ⋙
    (Functor.whiskeringLeft C C (ModuleCat.{v} R)).obj (shiftFunctor C n)

/-- Shifted morphisms into a fixed target, contravariantly functorial in their source. -/
@[stacks 0G1X "linear shifted Hom functor in the source"]
def sourceFunctor (Y : C) (n : ℤ) : Cᵒᵖ ⥤ ModuleCat.{v} R :=
  (linearYoneda R C).obj ((shiftFunctor C n).obj Y)

/-- Shifted morphisms from a fixed source, covariantly functorial in their target. -/
@[stacks 0G1X "linear shifted Hom functor in the target"]
def targetFunctor (X : C) (n : ℤ) : C ⥤ ModuleCat.{v} R :=
  shiftFunctor C n ⋙ (CategoryTheory.linearCoyoneda R C).obj (op X)

/-- The module-valued shifted-Hom bifunctor is additive in its source variable. -/
@[stacks 0G1X "additivity of the linear shifted Hom bifunctor"]
noncomputable instance linearCoyonedaAdditive (n : ℤ) :
    (linearCoyoneda R C n).Additive := sorry

/-- Shifted Hom into a fixed target is additive in the source. -/
@[stacks 0G1X "additivity of shifted Hom in the source"]
noncomputable instance sourceFunctorAdditive (Y : C) (n : ℤ) :
    (sourceFunctor R Y n).Additive := sorry

/-- Shifted Hom from a fixed source is additive in the target. -/
@[stacks 0G1X "additivity of shifted Hom in the target"]
noncomputable instance targetFunctorAdditive (X : C) (n : ℤ)
    [(shiftFunctor C n).Additive] :
    (targetFunctor R X n).Additive := sorry

section Linear

variable (S : Type uS) [CommRing S]
variable {D : Type u} [Category.{v} D] [Preadditive D] [CategoryTheory.Linear S D]
  [HasShift D ℤ]

/-- The module-valued shifted-Hom bifunctor is `S`-linear in its source variable. -/
@[stacks 0G1X "linearity of the linear shifted Hom bifunctor"]
noncomputable instance linearCoyonedaLinear (n : ℤ) :
    Functor.Linear S (linearCoyoneda S D n) := sorry

/-- Shifted Hom into a fixed target is `S`-linear in the source. -/
@[stacks 0G1X "linearity of shifted Hom in the source"]
noncomputable instance sourceFunctorLinear (Y : D) (n : ℤ) :
    Functor.Linear S (sourceFunctor S Y n) := sorry

/-- Shifted Hom from a fixed source is `S`-linear in the target. -/
@[stacks 0G1X "linearity of shifted Hom in the target"]
noncomputable instance targetFunctorLinear (X : D) (n : ℤ)
    [Functor.Linear S (shiftFunctor D n)] :
    Functor.Linear S (targetFunctor S X n) := sorry

end Linear

/-- A source morphism acts on fixed-source shifted Hom functors by precomposition. -/
@[stacks 0G1X "precomposition on fixed-source shifted Hom functors"]
def targetMap {X Y : C} (f : X ⟶ Y) (n : ℤ) :
    targetFunctor R Y n ⟶ targetFunctor R X n :=
  Functor.whiskerLeft (shiftFunctor C n) ((CategoryTheory.linearCoyoneda R C).map f.op)

/-- Precomposition by an isomorphism is an isomorphism of fixed-source shifted Hom
functors. -/
@[stacks 0G1X "isomorphism action on fixed-source shifted Hom functors"]
instance targetMap_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] (n : ℤ) :
    IsIso (targetMap R f n) := sorry

/-- Evaluating the shifted linear co-Yoneda functor at a source gives the fixed-source target
functor. -/
@[simp]
theorem linearCoyoneda_obj (X : Cᵒᵖ) (n : ℤ) :
    (ShiftedHom.linearCoyoneda R C n).obj X = targetFunctor R X.unop n := sorry

/-- The source action of the shifted linear co-Yoneda functor is the canonical precomposition
transformation. -/
@[simp]
theorem linearCoyoneda_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : ℤ) :
    (ShiftedHom.linearCoyoneda R C n).map f = targetMap R f.unop n := sorry

/-- The source action on shifted Hom is ordinary precomposition on elements. -/
@[simp]
theorem targetMap_app_apply {X Y : C} (f : X ⟶ Y) (Z : C) (n : ℤ)
    (g : ShiftedHom Y Z n) :
    ModuleCat.Hom.hom ((targetMap R f n).app Z) g = f ≫ g := sorry

/-- The identity source morphism acts by the identity natural transformation. -/
@[simp]
theorem targetMap_id (X : C) (n : ℤ) :
    targetMap R (𝟙 X) n = 𝟙 (targetFunctor R X n) := sorry

/-- Precomposition reverses composition of source morphisms. -/
@[simp]
theorem targetMap_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℤ) :
    targetMap R (f ≫ g) n = targetMap R g n ≫ targetMap R f n := sorry

/-- Isomorphic sources determine isomorphic fixed-source shifted Hom functors. -/
@[stacks 0G1X "fixed-source shifted Hom isomorphism"]
def targetIso {X Y : C} (e : X ≅ Y) (n : ℤ) :
    targetFunctor R X n ≅ targetFunctor R Y n where
  hom := targetMap R e.inv n
  inv := targetMap R e.hom n
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `targetIso` is precomposition by the inverse source isomorphism. -/
@[simp]
theorem targetIso_hom {X Y : C} (e : X ≅ Y) (n : ℤ) :
    (targetIso R e n).hom = targetMap R e.inv n := sorry

end CategoryTheory.ShiftedHom
