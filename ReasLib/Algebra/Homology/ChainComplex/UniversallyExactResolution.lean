module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact

@[expose] public section

open CategoryTheory

universe u v

namespace ModuleCat

variable {A : Type u} [CommRing A]

/-- A universally exact resolution of a module consists of an augmented nonnegative chain
complex that remains exact after tensoring with every module. -/
structure UniversallyExactResolution (N : ModuleCat.{v} A) where
  /-- The nonnegative chain complex underlying the resolution. -/
  complex : ChainComplex (ModuleCat.{v} A) ℕ
  /-- The augmentation from degree zero to the resolved module. -/
  π : complex.X 0 ⟶ N
  /-- The first differential followed by the augmentation vanishes. -/
  d_π : complex.d 1 0 ≫ π = 0
  /-- Tensoring the augmentation with any module preserves surjectivity. -/
  augmentationSurjective : ∀ (Q : Type (max u v)) [AddCommGroup Q] [Module A Q],
    Function.Surjective (π.hom.rTensor Q)
  /-- Exactness at degree zero is preserved by tensoring with every module. -/
  augmentationExact : ∀ (Q : Type (max u v)) [AddCommGroup Q] [Module A Q],
    LinearMap.range ((complex.d 1 0).hom.rTensor Q) =
      LinearMap.ker (π.hom.rTensor Q)
  /-- Exactness at every positive-degree middle term is preserved by tensoring with every
  module. -/
  predecessorExact : ∀ n (Q : Type (max u v)) [AddCommGroup Q] [Module A Q],
    LinearMap.range ((complex.d (n + 2) (n + 1)).hom.rTensor Q) =
      LinearMap.ker ((complex.d (n + 1) n).hom.rTensor Q)

namespace UniversallyExactResolution

variable {N : ModuleCat.{v} A}

/-- Construct a universally exact resolution from an augmented chain complex and its
tensor-stable surjectivity and exactness properties. -/
def of (complex : ChainComplex (ModuleCat.{v} A) ℕ) (π : complex.X 0 ⟶ N)
    (d_π : complex.d 1 0 ≫ π = 0)
    (augmentationSurjective : ∀ (Q : Type (max u v)) [AddCommGroup Q] [Module A Q],
      Function.Surjective (π.hom.rTensor Q))
    (augmentationExact : ∀ (Q : Type (max u v)) [AddCommGroup Q] [Module A Q],
      LinearMap.range ((complex.d 1 0).hom.rTensor Q) =
        LinearMap.ker (π.hom.rTensor Q))
    (predecessorExact : ∀ n (Q : Type (max u v)) [AddCommGroup Q] [Module A Q],
      LinearMap.range ((complex.d (n + 2) (n + 1)).hom.rTensor Q) =
        LinearMap.ker ((complex.d (n + 1) n).hom.rTensor Q)) :
    UniversallyExactResolution N :=
  { complex, π, d_π, augmentationSurjective, augmentationExact, predecessorExact }

/-- The tensor-stable surjectivity and exactness specification of a universally exact
resolution. -/
theorem spec (Q : UniversallyExactResolution N) :
    (∀ (T : Type (max u v)) [AddCommGroup T] [Module A T],
      Function.Surjective (Q.π.hom.rTensor T)) ∧
    (∀ (T : Type (max u v)) [AddCommGroup T] [Module A T],
      LinearMap.range ((Q.complex.d 1 0).hom.rTensor T) =
        LinearMap.ker (Q.π.hom.rTensor T)) ∧
    ∀ n (T : Type (max u v)) [AddCommGroup T] [Module A T],
      LinearMap.range ((Q.complex.d (n + 2) (n + 1)).hom.rTensor T) =
        LinearMap.ker ((Q.complex.d (n + 1) n).hom.rTensor T) := sorry

end UniversallyExactResolution

end ModuleCat
