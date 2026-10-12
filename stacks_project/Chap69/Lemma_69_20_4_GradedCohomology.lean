/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import ReasLib.Algebra.Group.Action.NatInt
public import ReasLib.Algebra.Module.Finite.Explicit
public import ReasLib.Algebra.Module.Graded.Decomposition
public import stacks_project.Chap69.«69_3_0_1_HigherDirectImage»
public import stacks_project.Chap69.Lemma_69_20_4_Pullback

/-!
# Graded cohomology of modules on algebraic spaces

This module constructs the total cohomology of a graded module over a pullback affine tilde
algebra, together with the induced action of the affine graded algebra.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.PullbackTilde
open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators DirectSum

noncomputable section

universe u

variable {S : Scheme.{u}}

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyOver`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.Modules

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

/-- A finite homogeneous family generates a graded module on an étale object when, after
restriction along every morphism `V ⟶ U`, each homogeneous section is a finite sum of the
restricted generators multiplied by complementary-degree algebra sections. -/
def HomogeneouslyGeneratesOn {X : AlgebraicSpace S} {𝓑 : ℤ → X.Modules}
    {alg : OXGradedAlgebra 𝓑} (F : GradedModule alg) (U : smallEtaleSite X) (r : ℕ)
    (degree : Fin r → ℤ)
    (generator : ∀ j : Fin r, (F.obj (degree j)).val.obj (Opposite.op U)) : Prop :=
  ∀ ⦃V : smallEtaleSite X⦄ (i : V ⟶ U) (n : ℤ) (x : (F.obj n).val.obj (Opposite.op V)),
    ∃ (coefficientDegree : Fin r → ℤ)
      (degree_eq : ∀ j : Fin r, degree j + coefficientDegree j = n)
      (coefficient : ∀ j : Fin r, (𝓑 (coefficientDegree j)).val.obj (Opposite.op V)),
      x = ∑ j : Fin r,
        cast (congrArg (fun k : ℤ ↦ ((F.obj k).val.obj (Opposite.op V) : Type u)) (degree_eq j))
          (F.smul (degree j) (coefficientDegree j) (Opposite.op V)
            (((F.obj (degree j)).val.map i.op).hom (generator j)) (coefficient j))

/-- Homogeneous generation on one étale object is the stated finite-sum criterion. -/
theorem homogeneouslyGeneratesOn_iff {X : AlgebraicSpace S} {𝓑 : ℤ → X.Modules}
    {alg : OXGradedAlgebra 𝓑} (F : GradedModule alg) (U : smallEtaleSite X) (r : ℕ)
    (degree : Fin r → ℤ)
    (generator : ∀ j : Fin r, (F.obj (degree j)).val.obj (Opposite.op U)) :
    HomogeneouslyGeneratesOn F U r degree generator ↔
      ∀ ⦃V : smallEtaleSite X⦄ (i : V ⟶ U) (n : ℤ) (x : (F.obj n).val.obj (Opposite.op V)),
        ∃ (coefficientDegree : Fin r → ℤ)
          (degree_eq : ∀ j : Fin r, degree j + coefficientDegree j = n)
          (coefficient : ∀ j : Fin r, (𝓑 (coefficientDegree j)).val.obj (Opposite.op V)),
          x = ∑ j : Fin r,
            cast (congrArg (fun k : ℤ ↦ ((F.obj k).val.obj (Opposite.op V) : Type u)) (degree_eq j))
              (F.smul (degree j) (coefficientDegree j) (Opposite.op V)
                (((F.obj (degree j)).val.map i.op).hom (generator j)) (coefficient j)) :=
  sorry

/-- A graded module is of finite type when a cover of the small étale site carries finite
homogeneous generating families. -/
def IsFiniteType {X : AlgebraicSpace S} {𝓑 : ℤ → X.Modules} {alg : OXGradedAlgebra 𝓑}
    (F : GradedModule alg) : Prop :=
  ∃ (I : Type u) (U : I → smallEtaleSite X),
    (smallEtaleTopology X).CoversTop U ∧
      ∀ i : I, ∃ (r : ℕ) (degree : Fin r → ℤ)
        (generator : ∀ j : Fin r, (F.obj (degree j)).val.obj (Opposite.op (U i))),
        HomogeneouslyGeneratesOn F (U i) r degree generator

/-- Finite type is exactly local finite homogeneous generation on the members of one cover. -/
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

namespace GradedCohomology

/-- Cohomology `H^i(X, ℱ)` as an `A`-module, realized as global sections of the scheme-module
image of `R^i f_* ℱ` on `Spec A`. -/
def cohomologyOver {A : Type u} [CommRing A] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] (ℱ : X.Modules) (i : ℕ) :
    ModuleCat A :=
  (moduleSpecΓFunctor (R := CommRingCat.of A)).obj
    ((toScheme (Over.mk σA)).obj (higherDirectImage f ℱ i))

/-- The map on affine-base cohomology induced by a morphism of modules. -/
def cohomologyOverMap {A : Type u} [CommRing A] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] {F G : X.Modules} (φ : F ⟶ G) (i : ℕ) :
    cohomologyOver σA f F i ⟶ cohomologyOver σA f G i :=
  (moduleSpecΓFunctor (R := CommRingCat.of A)).map
    ((toScheme (Over.mk σA)).map (higherDirectImageMap f φ i))

/-- `cohomologyOverMap` is global sections of `toScheme` of the higher direct image of `φ`. -/
theorem cohomologyOverMap_eq {A : Type u} [CommRing A] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] {F G : X.Modules} (φ : F ⟶ G) (i : ℕ) :
    cohomologyOverMap σA f φ i =
      (moduleSpecΓFunctor (R := CommRingCat.of A)).map
        ((toScheme (Over.mk σA)).map (higherDirectImageMap f φ i)) :=
  sorry

/-- The degree-`n` part of the degree-`p` cohomology of a graded module. -/
abbrev piece {A : Type u} [CommRing A] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] {𝓑 : ℤ → X.Modules} {alg : OXGradedAlgebra 𝓑}
    (F : GradedModule alg) (p : ℕ) (n : ℤ) : Type u :=
  (cohomologyOver σA f (F.obj n) p : Type u)

/-- The degree-`n` cohomology piece is the underlying type of `cohomologyOver`. -/
theorem piece_eq {A : Type u} [CommRing A] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] {𝓑 : ℤ → X.Modules} {alg : OXGradedAlgebra 𝓑}
    (F : GradedModule alg) (p : ℕ) (n : ℤ) :
    piece σA f F p n = (cohomologyOver σA f (F.obj n) p : Type u) :=
  sorry

/-- The total degree-`p` cohomology of a graded module is the direct sum of the cohomology of
its homogeneous pieces. -/
abbrev carrier {A : Type u} [CommRing A] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] {𝓑 : ℤ → X.Modules} {alg : OXGradedAlgebra 𝓑}
    (F : GradedModule alg) (p : ℕ) : Type u :=
  DirectSum ℤ fun n ↦ piece σA f F p n

/-- Total graded cohomology unfolds to the direct sum of the cohomology of the homogeneous
pieces. -/
theorem carrier_def {A : Type u} [CommRing A] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] {𝓑 : ℤ → X.Modules} {alg : OXGradedAlgebra 𝓑}
    (F : GradedModule alg) (p : ℕ) :
    carrier σA f F p = DirectSum ℤ fun n ↦ piece σA f F p n :=
  sorry

/-- The explicit homogeneous action on degreewise cohomology, with a scalar of degree `m`
sending the degree-`n` piece to the degree `m +ᵥ n` piece. -/
def smul {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] {𝓑 : ℤ → X.Modules}
    (pullbackData : Comparison 𝒜 σA f 𝓑) (F : GradedModule pullbackData.toOXGradedAlgebra) (p : ℕ)
    {m : ℕ} {n : ℤ} (b : 𝒜 m) (x : piece σA f F p n) :
    piece σA f F p (m +ᵥ n) :=
  ((cohomologyOverMap σA f
      (F.smulHom n (m : ℤ) (pullbackData.homogeneousSection m b) ≫
        eqToHom (congrArg F.obj
          ((add_comm n (m : ℤ)).trans (AddAction.nat_vadd_int m n).symm))) p).hom x)

/-- The degree-zero unit acts trivially on degreewise graded cohomology. -/
theorem one_smul {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] {𝓑 : ℤ → X.Modules}
    (pullbackData : Comparison 𝒜 σA f 𝓑) (F : GradedModule pullbackData.toOXGradedAlgebra) (p : ℕ)
    (x : GradedMonoid (piece σA f F p)) :
    GradedMonoid.mk (0 +ᵥ x.1)
      (smul 𝒜 σA f pullbackData F p (1 : 𝒜 0) x.2) = x :=
  sorry

/-- Successive homogeneous actions on degreewise cohomology agree with homogeneous
multiplication. -/
theorem mul_smul {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] {𝓑 : ℤ → X.Modules}
    (pullbackData : Comparison 𝒜 σA f 𝓑) (F : GradedModule pullbackData.toOXGradedAlgebra) (p : ℕ)
    (a b : GradedMonoid (fun d : ℕ ↦ 𝒜 d)) (x : GradedMonoid (piece σA f F p)) :
    GradedMonoid.mk ((a * b).1 +ᵥ x.1)
        (smul 𝒜 σA f pullbackData F p (a * b).2 x.2) =
      GradedMonoid.mk (a.1 +ᵥ (b.1 +ᵥ x.1))
        (smul 𝒜 σA f pullbackData F p a.2
          (smul 𝒜 σA f pullbackData F p b.2 x.2)) :=
  sorry

/-- A homogeneous scalar distributes over addition in a cohomology piece. -/
theorem smul_add {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] {𝓑 : ℤ → X.Modules}
    (pullbackData : Comparison 𝒜 σA f 𝓑) (F : GradedModule pullbackData.toOXGradedAlgebra) (p : ℕ)
    {m : ℕ} {n : ℤ} (b : 𝒜 m) (x y : piece σA f F p n) :
    smul 𝒜 σA f pullbackData F p b (x + y) =
      smul 𝒜 σA f pullbackData F p b x + smul 𝒜 σA f pullbackData F p b y :=
  sorry

/-- Every homogeneous scalar sends zero to zero in degreewise cohomology. -/
theorem smul_zero {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] {𝓑 : ℤ → X.Modules}
    (pullbackData : Comparison 𝒜 σA f 𝓑) (F : GradedModule pullbackData.toOXGradedAlgebra) (p : ℕ)
    {m : ℕ} {n : ℤ} (b : 𝒜 m) :
    smul 𝒜 σA f pullbackData F p b (0 : piece σA f F p n) = 0 :=
  sorry

/-- Addition of homogeneous scalars distributes through the degreewise cohomology action. -/
theorem add_smul {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] {𝓑 : ℤ → X.Modules}
    (pullbackData : Comparison 𝒜 σA f 𝓑) (F : GradedModule pullbackData.toOXGradedAlgebra) (p : ℕ)
    {m : ℕ} {n : ℤ} (a b : 𝒜 m) (x : piece σA f F p n) :
    smul 𝒜 σA f pullbackData F p (a + b) x =
      smul 𝒜 σA f pullbackData F p a x + smul 𝒜 σA f pullbackData F p b x :=
  sorry

/-- The zero homogeneous scalar acts by zero on every degreewise cohomology piece. -/
theorem zero_smul {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] {𝓑 : ℤ → X.Modules}
    (pullbackData : Comparison 𝒜 σA f 𝓑) (F : GradedModule pullbackData.toOXGradedAlgebra) (p : ℕ)
    {m : ℕ} {n : ℤ} (x : piece σA f F p n) :
    smul 𝒜 σA f pullbackData F p (0 : 𝒜 m) x = 0 :=
  sorry

/-- The graded action on cohomology induced by canonical homogeneous sections of a pullback
affine tilde algebra and multiplication on the graded module. -/
@[reducible]
def gmodule {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] {𝓑 : ℤ → X.Modules}
    (pullbackData : Comparison 𝒜 σA f 𝓑) (F : GradedModule pullbackData.toOXGradedAlgebra) (p : ℕ) :
    DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d) (piece σA f F p) where
  smul := smul 𝒜 σA f pullbackData F p
  one_smul := one_smul 𝒜 σA f pullbackData F p
  mul_smul := mul_smul 𝒜 σA f pullbackData F p
  smul_add := smul_add 𝒜 σA f pullbackData F p
  smul_zero := smul_zero 𝒜 σA f pullbackData F p
  add_smul := add_smul 𝒜 σA f pullbackData F p
  zero_smul := zero_smul 𝒜 σA f pullbackData F p

/-- The module structure on total graded cohomology obtained by restricting the induced graded
action along the homogeneous decomposition of the affine algebra. -/
@[reducible]
def module {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] {𝓑 : ℤ → X.Modules}
    (pullbackData : Comparison 𝒜 σA f 𝓑) (F : GradedModule pullbackData.toOXGradedAlgebra) (p : ℕ) :
    Module B (carrier σA f F p) :=
  DirectSum.Gmodule.moduleFor 𝒜 (piece σA f F p) (gmodule 𝒜 σA f pullbackData F p)

/-- Under `module`, a homogeneous scalar acts on a pure cohomology summand through `smul`. -/
theorem module_smul_of {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] {𝓑 : ℤ → X.Modules}
    (pullbackData : Comparison 𝒜 σA f 𝓑) (F : GradedModule pullbackData.toOXGradedAlgebra) (p : ℕ)
    {m : ℕ} {n : ℤ} (b : 𝒜 m) (x : piece σA f F p n) :
    (module 𝒜 σA f pullbackData F p).toSMul.smul (b : B)
        (DirectSum.of (piece σA f F p) n x) =
      DirectSum.of (piece σA f F p) (m +ᵥ n)
        (smul 𝒜 σA f pullbackData F p b x) :=
  sorry

end GradedCohomology

end AlgebraicGeometry.AlgebraicSpace.Modules
