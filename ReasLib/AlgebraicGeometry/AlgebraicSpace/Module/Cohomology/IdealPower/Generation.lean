/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.IdealPower
public import ReasLib.Algebra.Module.IdealPower.Submodule.Tensor

/-!
# Generation bounds for ideal-power cohomology

Affine-base cohomology of the products `I^n F` carries a named multiplication map
`I^(n-c) ⊗ H^p(X, I^c F) ⟶ H^p(X, I^n F)` and a transition
`H^p(X, I^(n+m) F) ⟶ H^p(X, I^n F)`. A generation bound is a single `c`
making multiplication surjective for `n ≥ c` and sending transition images into
`I^(m-c) H^p(X, I^n F)` for `m ≥ c`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u

variable {A : Type u} [CommRing A]
variable {X : AlgebraicSpace (Spec (CommRingCat.of A))}

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyOver`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology

/-- The product `I^m F` is contained in `I^n F` whenever `n ≤ m`. -/
theorem product_le (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    {m n : ℕ} (h : m ≤ n) :
    product I f F n ≤ product I f F m :=
  sorry

/-- The inclusion `I^n F ⟶ I^m F` of ideal-power products for `m ≤ n`. -/
def productInclusion (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    {m n : ℕ} (h : m ≤ n) :
    (product I f F n : X.Modules) ⟶ (product I f F m : X.Modules) :=
  Subobject.ofLE (product I f F n) (product I f F m) (product_le I f F h)

/-- `productInclusion` is the `Subobject.ofLE` map of `product_le`. -/
theorem productInclusion_eq (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    {m n : ℕ} (h : m ≤ n) :
    productInclusion I f F h =
      Subobject.ofLE (product I f F n) (product I f F m) (product_le I f F h) :=
  sorry

/-- Degree-adjusted action `I^(n-c) ⊗ I^c F → I^n F`, reindexing `(n-c)+c = n`. -/
def actionMapTo (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    (c n : ℕ) (h : c ≤ n) (a : (I ^ (n - c) : Ideal A)) :
    (product I f F c : X.Modules) ⟶ (product I f F n : X.Modules) :=
  actionMap I f F a ≫
    eqToHom (congrArg (fun k ↦ (product I f F k : X.Modules)) (Nat.sub_add_cancel h))

/-- `actionMapTo` is `actionMap` followed by reindexing `(n-c)+c = n`. -/
theorem actionMapTo_eq (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    (c n : ℕ) (h : c ≤ n) (a : (I ^ (n - c) : Ideal A)) :
    actionMapTo I f F c n h a =
      actionMap I f F a ≫
        eqToHom (congrArg (fun k ↦ (product I f F k : X.Modules))
          (Nat.sub_add_cancel h)) :=
  sorry

/-- The cohomology object `H^p(X, I^n F)` as an `A`-module. -/
abbrev stage (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) : ModuleCat A :=
  GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f
    (product I f F n : X.Modules) p

/-- Stage cohomology is affine-base cohomology of the corresponding product. -/
theorem stage_eq (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    stage I f F p n =
      GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f
        (product I f F n : X.Modules) p :=
  sorry

/-- The canonical transition `H^p(X, I^n F) ⟶ H^p(X, I^m F)` for `m ≤ n`. -/
def transition (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) {m n : ℕ} (h : m ≤ n) :
    stage I f F p n ⟶ stage I f F p m :=
  GradedCohomology.cohomologyOverMap (𝟙 (Spec (CommRingCat.of A))) f
    (productInclusion I f F h) p

/-- Every cohomology transition is cohomology of the corresponding product inclusion. -/
theorem transition_eq (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) {m n : ℕ} (h : m ≤ n) :
    transition I f F p h =
      GradedCohomology.cohomologyOverMap (𝟙 (Spec (CommRingCat.of A))) f
        (productInclusion I f F h) p :=
  sorry

/-- Coefficient action of `a : I^(n-c)` on `H^p(X, I^c F)`. -/
def mulMapApp (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p c n : ℕ) (h : c ≤ n)
    (a : (I ^ (n - c) : Ideal A)) :
    stage I f F p c ⟶ stage I f F p n :=
  GradedCohomology.cohomologyOverMap (𝟙 (Spec (CommRingCat.of A))) f
    (actionMapTo I f F c n h a) p

/-- Evaluating the coefficient action recovers cohomology of the sheaf-level action. -/
theorem mulMapApp_eq (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p c n : ℕ) (h : c ≤ n)
    (a : (I ^ (n - c) : Ideal A)) :
    mulMapApp I f F p c n h a =
      GradedCohomology.cohomologyOverMap (𝟙 (Spec (CommRingCat.of A))) f
        (actionMapTo I f F c n h a) p :=
  sorry

/-- The cohomological coefficient action is additive in the ideal coefficient. -/
theorem mulMapApp_add (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p c n : ℕ) (h : c ≤ n)
    (a b : (I ^ (n - c) : Ideal A)) :
    (mulMapApp I f F p c n h (a + b)).hom =
      (mulMapApp I f F p c n h a).hom + (mulMapApp I f F p c n h b).hom :=
  sorry

/-- The cohomological coefficient action is linear over the affine base ring. -/
theorem mulMapApp_smul (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p c n : ℕ) (h : c ≤ n)
    (r : A) (a : (I ^ (n - c) : Ideal A)) :
    (mulMapApp I f F p c n h (r • a)).hom =
      r • (mulMapApp I f F p c n h a).hom :=
  sorry

/-- The bilinear action of ideal coefficients on ideal-power cohomology. -/
def mulMapBilinear (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p c n : ℕ) (h : c ≤ n) :
    (I ^ (n - c) : Ideal A) →ₗ[A] stage I f F p c →ₗ[A] stage I f F p n where
  toFun a := (mulMapApp I f F p c n h a).hom
  map_add' := mulMapApp_add I f F p c n h
  map_smul' := mulMapApp_smul I f F p c n h

/-- The Rees multiplication `I^(n-c) ⊗ H^p(X, I^c F) ⟶ H^p(X, I^n F)` for `n ≥ c`. -/
def mulMap (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p c n : ℕ) (h : c ≤ n) :
    (tensorLeft (ModuleCat.of A (I ^ (n - c) : Ideal A))).obj (stage I f F p c) ⟶
      stage I f F p n :=
  ModuleCat.ofHom (Y := stage I f F p n)
    (TensorProduct.lift (mulMapBilinear I f F p c n h))

/-- The Rees multiplication map is the tensor-lift of the coefficient actions. -/
theorem mulMap_eq (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p c n : ℕ) (h : c ≤ n) :
    mulMap I f F p c n h = ModuleCat.ofHom (Y := stage I f F p n)
    (TensorProduct.lift (mulMapBilinear I f F p c n h)) :=
  sorry

/-- Multiplication on a pure tensor is the canonical cohomological coefficient action. -/
theorem mulMap_tmul (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p c n : ℕ) (h : c ≤ n)
    (a : (I ^ (n - c) : Ideal A)) (x : stage I f F p c) :
    (mulMap I f F p c n h).hom (a ⊗ₜ[A] x) =
      (mulMapApp I f F p c n h a).hom x :=
  sorry

/-- A single integer `c` witnessing both generation clauses for `H^p(X, I^n F)`. -/
structure IsGenerationBound (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p c : ℕ) : Prop where
  /-- Clause (1): Rees multiplication is surjective for every `n ≥ c`. -/
  mul_surjective :
    ∀ (n : ℕ) (hn : c ≤ n), Function.Surjective (mulMap I f F p c n hn).hom
  /-- Clause (2): images of `H^p(I^(n+m) F) ⟶ H^p(I^n F)` lie in `I^(m-c) H^p(I^n F)`
  for `m ≥ c`. -/
  image_le :
    ∀ (n m : ℕ), c ≤ m →
      LinearMap.range (transition I f F p (Nat.le_add_right n m)).hom ≤
        Ideal.PowerSubmodule.stage I (stage I f F p n) (m - c)

/-- Packages the two generation clauses at a shared bound `c`. -/
def IsGenerationBound.of (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p c : ℕ)
    (mul_surjective :
      ∀ (n : ℕ) (hn : c ≤ n), Function.Surjective (mulMap I f F p c n hn).hom)
    (image_le :
      ∀ (n m : ℕ), c ≤ m →
        LinearMap.range (transition I f F p (Nat.le_add_right n m)).hom ≤
          Ideal.PowerSubmodule.stage I (stage I f F p n) (m - c)) :
    IsGenerationBound I f F p c where
  mul_surjective := mul_surjective
  image_le := image_le

/-- The two defining conditions of a generation bound, exposed together. -/
theorem isGenerationBound_iff (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p c : ℕ) :
    IsGenerationBound I f F p c ↔
      (∀ (n : ℕ) (hn : c ≤ n), Function.Surjective (mulMap I f F p c n hn).hom) ∧
        (∀ (n m : ℕ), c ≤ m →
          LinearMap.range (transition I f F p (Nat.le_add_right n m)).hom ≤
            Ideal.PowerSubmodule.stage I (stage I f F p n) (m - c)) :=
  sorry

/-- For a coherent module on an algebraic space proper over a Noetherian affine base,
every cohomological degree admits a bound giving surjective ideal-power multiplication
and ideal-power containment of all sufficiently separated transition images. -/
theorem exists_isGenerationBound [IsNoetherianRing A] (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
    (F : X.Modules) [F.IsCoherent]
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    ∃ c : ℕ, IsGenerationBound I f F p c :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology
