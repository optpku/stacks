module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.Group.Action.NatInt
public import ReasLib.Algebra.Module.Finite.Explicit
public import ReasLib.Algebra.Module.Graded.Decomposition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Graded.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.OverAffine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper

/-! # Graded cohomology and finiteness over an affine base -/

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

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyOver`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace GradedCohomology

/-- Cohomology `H^i(X, ℱ)` as an `A`-module, realized as global sections of the scheme-module
image of `R^i f_* ℱ` on `Spec A`. -/
abbrev cohomologyOver {A : Type u} [CommRing A] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] (ℱ : X.Modules) (i : ℕ) :
    ModuleCat A :=
  AlgebraicGeometry.AlgebraicSpace.Modules.cohomologyOver σA f ℱ i

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

/-- If `A` is a Noetherian ring, `B` is a finitely generated graded `A`-algebra,
`f : X ⟶ ofOver (Over.mk σA)` is a proper morphism of algebraic spaces to `Spec(A)` over a
scheme `S`, `𝓑` is identified with `f^*(tilde B)` by a pullback-tilde comparison, and `F` is a
quasi-coherent graded `𝓑`-module of finite type, then for every `p : ℕ` the graded `B`-module
`carrier σA f F p` is a finite `B`-module under the canonical action `module`. Here
`ofOver (Over.mk σA)` is `Spec(A)` as an algebraic space over `S`, and `carrier` is the
graded `B`-module `H^p(X, F)`. -/
@[stacks 08AT]
theorem finite {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] [Algebra.FiniteType A B]
    {X : AlgebraicSpace S} (σA : Spec (CommRingCat.of A) ⟶ S)
    (f : X ⟶ ofOver (Over.mk σA)) [Proper f]
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] (𝓑 : ℤ → X.Modules)
    (pullbackData : Comparison 𝒜 σA f 𝓑) (F : GradedModule pullbackData.toOXGradedAlgebra)
    (hFQuasicoherent : ∀ n : ℤ, (F.obj n).IsQuasicoherent)
    (hFFiniteType : F.IsFiniteType) (p : ℕ) :
    Module.FiniteWithAction B (carrier σA f F p) (module 𝒜 σA f pullbackData F p) :=
  sorry

end GradedCohomology

end AlgebraicGeometry.AlgebraicSpace.Modules
