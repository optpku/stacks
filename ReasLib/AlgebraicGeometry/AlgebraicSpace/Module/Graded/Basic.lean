module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Graded.Pullback

/-! # Graded modules and local finite homogeneous generation on algebraic spaces -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.PullbackTilde
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open SheafOfModules
open scoped BigOperators DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- A graded module over a degreewise `𝒪_X`-algebra on an algebraic space, given by a
degreewise family of coefficient modules and an `𝒪_X`-linear restriction-compatible action. -/
structure GradedModule {X : AlgebraicSpace S} {𝓑 : ℤ → X.Modules}
    (alg : OXGradedAlgebra 𝓑) where
  /-- The degreewise family of coefficient modules. -/
  obj : ℤ → X.Modules
  /-- The local `𝒪_X`-bilinear homogeneous action. -/
  smul : ∀ (n m : ℤ) (U : (smallEtaleSite X)ᵒᵖ),
    (obj n).val.obj U → (𝓑 m).val.obj U → (obj (n + m)).val.obj U
  /-- The action maps commute with restriction. -/
  map_smul : ∀ {n m : ℤ} {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V)
      (x : (obj n).val.obj U) (a : (𝓑 m).val.obj U),
      ((obj (n + m)).val.map i).hom (smul n m U x a) =
        smul n m V (((obj n).val.map i).hom x) (((𝓑 m).val.map i).hom a)
  /-- The action is additive in the coefficient module. -/
  smul_add : ∀ (n m : ℤ) (U : (smallEtaleSite X)ᵒᵖ)
      (x y : (obj n).val.obj U) (a : (𝓑 m).val.obj U),
      smul n m U (x + y) a = smul n m U x a + smul n m U y a
  /-- The action is additive in the algebra section. -/
  add_smul : ∀ (n m : ℤ) (U : (smallEtaleSite X)ᵒᵖ)
      (x : (obj n).val.obj U) (a b : (𝓑 m).val.obj U),
      smul n m U x (a + b) = smul n m U x a + smul n m U x b
  /-- The action is `𝒪_X`-linear in the coefficient module. -/
  smul_smul : ∀ (n m : ℤ) (U : (smallEtaleSite X)ᵒᵖ)
      (r : (structureSheaf X).obj.obj U) (x : (obj n).val.obj U) (a : (𝓑 m).val.obj U),
      smul n m U (r • x) a = r • smul n m U x a
  /-- The action is `𝒪_X`-linear in the algebra section. -/
  smul_smul_right : ∀ (n m : ℤ) (U : (smallEtaleSite X)ᵒᵖ)
      (r : (structureSheaf X).obj.obj U) (x : (obj n).val.obj U) (a : (𝓑 m).val.obj U),
      smul n m U x (r • a) = r • smul n m U x a
  /-- The action is associative with the graded multiplication on the algebra. -/
  smul_assoc : ∀ (n m l : ℤ) (U : (smallEtaleSite X)ᵒᵖ)
      (x : (obj n).val.obj U) (a : (𝓑 m).val.obj U) (b : (𝓑 l).val.obj U),
      HEq (smul (n + m) l U (smul n m U x a) b) (smul n (m + l) U x (alg.mul U m l a b))
  /-- The degree-zero unit section acts trivially. -/
  smul_one : ∀ (n : ℤ) (U : (smallEtaleSite X)ᵒᵖ) (x : (obj n).val.obj U),
      HEq (smul n 0 U x (alg.one U)) x

namespace GradedModule

/-- Constructs a graded module from a degreewise family and an `𝒪_X`-linear action. -/
def ofComponents {X : AlgebraicSpace S} {𝓑 : ℤ → X.Modules} (alg : OXGradedAlgebra 𝓑)
    (obj : ℤ → X.Modules)
    (smul : ∀ (n m : ℤ) (U : (smallEtaleSite X)ᵒᵖ),
      (obj n).val.obj U → (𝓑 m).val.obj U → (obj (n + m)).val.obj U)
    (map_smul : ∀ {n m : ℤ} {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V)
      (x : (obj n).val.obj U) (a : (𝓑 m).val.obj U),
      ((obj (n + m)).val.map i).hom (smul n m U x a) =
        smul n m V (((obj n).val.map i).hom x) (((𝓑 m).val.map i).hom a))
    (smul_add : ∀ (n m : ℤ) (U : (smallEtaleSite X)ᵒᵖ)
      (x y : (obj n).val.obj U) (a : (𝓑 m).val.obj U),
      smul n m U (x + y) a = smul n m U x a + smul n m U y a)
    (add_smul : ∀ (n m : ℤ) (U : (smallEtaleSite X)ᵒᵖ)
      (x : (obj n).val.obj U) (a b : (𝓑 m).val.obj U),
      smul n m U x (a + b) = smul n m U x a + smul n m U x b)
    (smul_smul : ∀ (n m : ℤ) (U : (smallEtaleSite X)ᵒᵖ)
      (r : (structureSheaf X).obj.obj U) (x : (obj n).val.obj U) (a : (𝓑 m).val.obj U),
      smul n m U (r • x) a = r • smul n m U x a)
    (smul_smul_right : ∀ (n m : ℤ) (U : (smallEtaleSite X)ᵒᵖ)
      (r : (structureSheaf X).obj.obj U) (x : (obj n).val.obj U) (a : (𝓑 m).val.obj U),
      smul n m U x (r • a) = r • smul n m U x a)
    (smul_assoc : ∀ (n m l : ℤ) (U : (smallEtaleSite X)ᵒᵖ)
      (x : (obj n).val.obj U) (a : (𝓑 m).val.obj U) (b : (𝓑 l).val.obj U),
      HEq (smul (n + m) l U (smul n m U x a) b) (smul n (m + l) U x (alg.mul U m l a b)))
    (smul_one : ∀ (n : ℤ) (U : (smallEtaleSite X)ᵒᵖ) (x : (obj n).val.obj U),
      HEq (smul n 0 U x (alg.one U)) x) :
    GradedModule alg :=
  { obj := obj
    smul := smul
    map_smul := map_smul
    smul_add := smul_add
    add_smul := add_smul
    smul_smul := smul_smul
    smul_smul_right := smul_smul_right
    smul_assoc := smul_assoc
    smul_one := smul_one }

/-- The action package of a graded module: restriction, associativity, and the unit law. -/
theorem spec {X : AlgebraicSpace S} {𝓑 : ℤ → X.Modules} {alg : OXGradedAlgebra 𝓑}
    (F : GradedModule alg) :
    (∀ {n m : ℤ} {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V)
      (x : (F.obj n).val.obj U) (a : (𝓑 m).val.obj U),
      ((F.obj (n + m)).val.map i).hom (F.smul n m U x a) =
        F.smul n m V (((F.obj n).val.map i).hom x) (((𝓑 m).val.map i).hom a)) ∧
    (∀ (n m l : ℤ) (U : (smallEtaleSite X)ᵒᵖ)
      (x : (F.obj n).val.obj U) (a : (𝓑 m).val.obj U) (b : (𝓑 l).val.obj U),
      HEq (F.smul (n + m) l U (F.smul n m U x a) b)
        (F.smul n (m + l) U x (alg.mul U m l a b))) ∧
    (∀ (n : ℤ) (U : (smallEtaleSite X)ᵒᵖ) (x : (F.obj n).val.obj U),
      HEq (F.smul n 0 U x (alg.one U)) x) :=
  sorry

/-- Multiplication by a compatible algebra section induces a degree-shifting morphism of
coefficient modules. -/
def smulHom {X : AlgebraicSpace S} {𝓑 : ℤ → X.Modules} {alg : OXGradedAlgebra 𝓑}
    (F : GradedModule alg) (n m : ℤ) (s : (𝓑 m).sections) : F.obj n ⟶ F.obj (n + m) :=
  ⟨{ app := fun U ↦
      ModuleCat.ofHom
        { toFun := fun x ↦ F.smul n m U x (s.1 U)
          map_add' := fun x y ↦ F.smul_add n m U x y (s.1 U)
          map_smul' := fun r x ↦ F.smul_smul n m U r x (s.1 U) }
     naturality := sorry }⟩

/-- Evaluating `smulHom` on local sections recovers the local action. -/
theorem smulHom_apply {X : AlgebraicSpace S} {𝓑 : ℤ → X.Modules} {alg : OXGradedAlgebra 𝓑}
    (F : GradedModule alg) (n m : ℤ) (s : (𝓑 m).sections) (U : (smallEtaleSite X)ᵒᵖ)
    (x : (F.obj n).val.obj U) :
    (F.smulHom n m s).val.app U x = F.smul n m U x (s.1 U) :=
  sorry

/-- A fixed finite homogeneous family generates on an étale object if every homogeneous
section over an object above it admits a coefficient expression on a covering sieve.
The generating family is independent of the degree, section, and covering sieve. -/
def HomogeneouslyGeneratesOn {X : AlgebraicSpace S} {𝓑 : ℤ → X.Modules}
    {alg : OXGradedAlgebra 𝓑} (F : GradedModule alg) (U : smallEtaleSite X) (r : ℕ)
    (degree : Fin r → ℤ)
    (generator : ∀ j : Fin r, (F.obj (degree j)).val.obj (Opposite.op U)) : Prop :=
  ∀ ⦃V : smallEtaleSite X⦄ (i : V ⟶ U) (n : ℤ) (x : (F.obj n).val.obj (Opposite.op V)),
    ∃ (cover : Sieve V), cover ∈ smallEtaleTopology X V ∧
      ∀ ⦃W : smallEtaleSite X⦄ (restriction : W ⟶ V), cover restriction →
        ∃ (coefficientDegree : Fin r → ℤ)
          (degree_eq : ∀ j : Fin r, degree j + coefficientDegree j = n)
          (coefficient : ∀ j : Fin r, (𝓑 (coefficientDegree j)).val.obj (Opposite.op W)),
          (((F.obj n).val.map restriction.op).hom x) = ∑ j : Fin r,
            cast (congrArg (fun k : ℤ ↦ ((F.obj k).val.obj (Opposite.op W) : Type u)) (degree_eq j))
              (F.smul (degree j) (coefficientDegree j) (Opposite.op W)
                (((F.obj (degree j)).val.map (restriction ≫ i).op).hom (generator j))
                (coefficient j))

/-- Homogeneous generation is the covering-local finite coefficient expression criterion. -/
theorem homogeneouslyGeneratesOn_iff {X : AlgebraicSpace S} {𝓑 : ℤ → X.Modules}
    {alg : OXGradedAlgebra 𝓑} (F : GradedModule alg) (U : smallEtaleSite X) (r : ℕ)
    (degree : Fin r → ℤ)
    (generator : ∀ j : Fin r, (F.obj (degree j)).val.obj (Opposite.op U)) :
    HomogeneouslyGeneratesOn F U r degree generator ↔
      ∀ ⦃V : smallEtaleSite X⦄ (i : V ⟶ U) (n : ℤ) (x : (F.obj n).val.obj (Opposite.op V)),
        ∃ (cover : Sieve V), cover ∈ smallEtaleTopology X V ∧
          ∀ ⦃W : smallEtaleSite X⦄ (restriction : W ⟶ V), cover restriction →
            ∃ (coefficientDegree : Fin r → ℤ)
              (degree_eq : ∀ j : Fin r, degree j + coefficientDegree j = n)
              (coefficient : ∀ j : Fin r, (𝓑 (coefficientDegree j)).val.obj (Opposite.op W)),
              (((F.obj n).val.map restriction.op).hom x) = ∑ j : Fin r,
                cast (congrArg (fun k : ℤ ↦ ((F.obj k).val.obj (Opposite.op W) : Type u)) (degree_eq j))
                  (F.smul (degree j) (coefficientDegree j) (Opposite.op W)
                    (((F.obj (degree j)).val.map (restriction ≫ i).op).hom (generator j))
                    (coefficient j)) :=
  sorry

/-- A graded module is of finite type if a cover of the small étale site carries finite
homogeneous families whose restrictions generate sections locally on covering sieves.
One generating family on each cover member serves all degrees and sections. -/
def IsFiniteType {X : AlgebraicSpace S} {𝓑 : ℤ → X.Modules} {alg : OXGradedAlgebra 𝓑}
    (F : GradedModule alg) : Prop :=
  ∃ (I : Type u) (U : I → smallEtaleSite X),
    (smallEtaleTopology X).CoversTop U ∧
      ∀ i : I, ∃ (r : ℕ) (degree : Fin r → ℤ)
        (generator : ∀ j : Fin r, (F.obj (degree j)).val.obj (Opposite.op (U i))),
        HomogeneouslyGeneratesOn F (U i) r degree generator

/-- Finite type is finite homogeneous generation on a cover, with coefficient expressions
local on covering sieves above each member. -/
theorem isFiniteType_iff {X : AlgebraicSpace S} {𝓑 : ℤ → X.Modules} {alg : OXGradedAlgebra 𝓑}
    (F : GradedModule alg) :
    IsFiniteType F ↔
      ∃ (I : Type u) (U : I → smallEtaleSite X),
        (smallEtaleTopology X).CoversTop U ∧
          ∀ i : I, ∃ (r : ℕ) (degree : Fin r → ℤ)
            (generator : ∀ j : Fin r, (F.obj (degree j)).val.obj (Opposite.op (U i))),
            HomogeneouslyGeneratesOn F (U i) r degree generator :=
  sorry

end GradedModule

end AlgebraicGeometry.AlgebraicSpace.Modules
