/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.Algebra.Module.IdealPower.Submodule.Tensor
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap69.Lemma_69_13_4_Product
public import stacks_project.Chap69.Lemma_69_20_4_GradedCohomology
public import stacks_project.Chap69.Lemma_69_22_2_IdealPower

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

/-- Tensor-lift of a family of maps out of a coefficient ideal, generic in the
`ModuleCat` source and target so the `A`-module structure is not unfolded. -/
def tensorLiftIdeal (I : Ideal A) (k : ℕ) {M N : ModuleCat A}
    (action : (I ^ k : Ideal A) → (M ⟶ N)) :
    (tensorLeft (ModuleCat.of A (I ^ k : Ideal A))).obj M ⟶ N :=
  ModuleCat.ofHom
    (TensorProduct.lift
      { toFun := fun a ↦ (action a).hom
        map_add' := sorry
        map_smul' := sorry })

/-- Tensor-lift is unchanged if the coefficient actions agree. -/
theorem tensorLiftIdeal_eq (I : Ideal A) (k : ℕ) {M N : ModuleCat A}
    {action action' : (I ^ k : Ideal A) → (M ⟶ N)} (h : action = action') :
    tensorLiftIdeal I k action = tensorLiftIdeal I k action' :=
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

/-- Affine-base cohomology of `I^n F` carries its `A`-module structure from `ModuleCat A`. -/
instance module_stage (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    Module A (stage I f F p n) :=
  ModuleCat.isModule (stage I f F p n)

/-- Affine-base cohomology of `I^n F` is an abelian group via its `ModuleCat` carrier. -/
instance addCommGroup_stage (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    AddCommGroup (stage I f F p n) :=
  ModuleCat.isAddCommGroup (stage I f F p n)

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

/-- The Rees multiplication `I^(n-c) ⊗ H^p(X, I^c F) ⟶ H^p(X, I^n F)` for `n ≥ c`. -/
def mulMap (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p c n : ℕ) (h : c ≤ n) :
    (tensorLeft (ModuleCat.of A (I ^ (n - c) : Ideal A))).obj (stage I f F p c) ⟶
      stage I f F p n :=
  tensorLiftIdeal I (n - c) (mulMapApp I f F p c n h)

/-- The Rees multiplication map is the tensor-lift of the coefficient actions. -/
theorem mulMap_eq (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p c n : ℕ) (h : c ≤ n) :
    mulMap I f F p c n h = tensorLiftIdeal I (n - c) (mulMapApp I f F p c n h) :=
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

/-- In Situation 69.22.1, every cohomological degree admits a generation bound. -/
theorem exists_isGenerationBound [IsNoetherianRing A] (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
    (F : X.Modules) [F.IsCoherent]
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    ∃ c : ℕ, IsGenerationBound I f F p c :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology
