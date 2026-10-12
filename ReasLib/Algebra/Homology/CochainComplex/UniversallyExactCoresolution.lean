/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import ReasLib.LinearAlgebra.UniversallyInjective

@[expose] public section

open CategoryTheory

universe u v

namespace ModuleCat

variable {A : Type u} [CommRing A]

/-- A universally exact coresolution of `M` is an augmented nonnegative cochain complex
whose augmentation is universally injective and which remains exact at every term after
tensoring with any `A`-module. -/
structure UniversallyExactCoresolution (M : ModuleCat.{v} A) where
  /-- The nonnegative cochain complex underlying the coresolution. -/
  cocomplex : CochainComplex (ModuleCat.{v} A) ℕ
  /-- The augmentation into degree zero. -/
  ι : M ⟶ cocomplex.X 0
  /-- The augmentation followed by the first differential vanishes. -/
  ι_d : ι ≫ cocomplex.d 0 1 = 0
  /-- Tensoring the augmentation with any module preserves injectivity. -/
  augmentationInjective :
    LinearMap.UniversallyInjective.{u, v, v, max u v} ι.hom
  /-- Exactness at degree zero is preserved by tensoring with every module. -/
  augmentationExact : ∀ (Q : Type (max u v)) [AddCommGroup Q] [Module A Q],
    LinearMap.range (ι.hom.rTensor Q) =
      LinearMap.ker ((cocomplex.d 0 1).hom.rTensor Q)
  /-- Exactness at every positive-degree middle term is preserved by tensoring with every
  module. -/
  successorExact : ∀ n (Q : Type (max u v)) [AddCommGroup Q] [Module A Q],
    LinearMap.range ((cocomplex.d n (n + 1)).hom.rTensor Q) =
      LinearMap.ker ((cocomplex.d (n + 1) (n + 2)).hom.rTensor Q)

namespace UniversallyExactCoresolution

variable {M : ModuleCat.{v} A}

/-- Construct a universally exact coresolution from its explicit cocomplex, augmentation,
and tensor-stable exactness properties. -/
def of (cocomplex : CochainComplex (ModuleCat.{v} A) ℕ) (ι : M ⟶ cocomplex.X 0)
    (ι_d : ι ≫ cocomplex.d 0 1 = 0)
    (augmentationInjective :
      LinearMap.UniversallyInjective.{u, v, v, max u v} ι.hom)
    (augmentationExact : ∀ (Q : Type (max u v)) [AddCommGroup Q] [Module A Q],
      LinearMap.range (ι.hom.rTensor Q) =
        LinearMap.ker ((cocomplex.d 0 1).hom.rTensor Q))
    (successorExact : ∀ n (Q : Type (max u v)) [AddCommGroup Q] [Module A Q],
      LinearMap.range ((cocomplex.d n (n + 1)).hom.rTensor Q) =
        LinearMap.ker ((cocomplex.d (n + 1) (n + 2)).hom.rTensor Q)) :
    UniversallyExactCoresolution M :=
  { cocomplex, ι, ι_d, augmentationInjective, augmentationExact, successorExact }

/-- The tensor-stable injectivity and exactness specification of a universally exact
coresolution. -/
theorem spec (P : UniversallyExactCoresolution M) :
    LinearMap.UniversallyInjective.{u, v, v, max u v} P.ι.hom ∧
    (∀ (Q : Type (max u v)) [AddCommGroup Q] [Module A Q],
      LinearMap.range (P.ι.hom.rTensor Q) =
        LinearMap.ker ((P.cocomplex.d 0 1).hom.rTensor Q)) ∧
    ∀ n (Q : Type (max u v)) [AddCommGroup Q] [Module A Q],
      LinearMap.range ((P.cocomplex.d n (n + 1)).hom.rTensor Q) =
        LinearMap.ker ((P.cocomplex.d (n + 1) (n + 2)).hom.rTensor Q) := sorry

end UniversallyExactCoresolution

end ModuleCat
