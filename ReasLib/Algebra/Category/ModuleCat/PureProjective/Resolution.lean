/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.PureProjective.Presentation
public import ReasLib.Algebra.Homology.ChainComplex.UniversallyExactResolution

@[expose] public section

open CategoryTheory

universe u v

namespace ModuleCat

variable {A : Type u} [CommRing A]

/-- A pure projective resolution is a universally exact resolution whose module in every
degree is pure projective. -/
structure PureProjectiveResolution (M : ModuleCat.{v} A)
    extends UniversallyExactResolution M where
  /-- Every term of the resolution is pure projective. -/
  pureProjective : ∀ n, (complex.X n).PureProjective

namespace PureProjectiveResolution

variable {M : ModuleCat.{v} A}

/-- Construct a pure projective resolution from an augmented chain complex, termwise pure
projectivity, and tensor-stable surjectivity and exactness. -/
def of (complex : ChainComplex (ModuleCat.{v} A) ℕ) (π : complex.X 0 ⟶ M)
    (d_π : complex.d 1 0 ≫ π = 0)
    (pureProjective : ∀ n, (complex.X n).PureProjective)
    (augmentationSurjective : ∀ (Q : Type (max u v)) [AddCommGroup Q] [Module A Q],
      Function.Surjective (π.hom.rTensor Q))
    (augmentationExact : ∀ (Q : Type (max u v)) [AddCommGroup Q] [Module A Q],
      LinearMap.range ((complex.d 1 0).hom.rTensor Q) =
        LinearMap.ker (π.hom.rTensor Q))
    (predecessorExact : ∀ n (Q : Type (max u v)) [AddCommGroup Q] [Module A Q],
      LinearMap.range ((complex.d (n + 2) (n + 1)).hom.rTensor Q) =
        LinearMap.ker ((complex.d (n + 1) n).hom.rTensor Q)) :
    PureProjectiveResolution M :=
  { toUniversallyExactResolution :=
      UniversallyExactResolution.of complex π d_π augmentationSurjective augmentationExact
        predecessorExact
    pureProjective }

/-- Termwise pure projectivity and tensor-stable surjectivity and exactness characterize a
pure projective resolution. -/
theorem spec (P : PureProjectiveResolution M) :
    (∀ n, (P.complex.X n).PureProjective) ∧
    (∀ (Q : Type (max u v)) [AddCommGroup Q] [Module A Q],
      Function.Surjective (P.π.hom.rTensor Q)) ∧
    (∀ (Q : Type (max u v)) [AddCommGroup Q] [Module A Q],
      LinearMap.range ((P.complex.d 1 0).hom.rTensor Q) =
        LinearMap.ker (P.π.hom.rTensor Q)) ∧
    ∀ n (Q : Type (max u v)) [AddCommGroup Q] [Module A Q],
      LinearMap.range ((P.complex.d (n + 2) (n + 1)).hom.rTensor Q) =
        LinearMap.ker ((P.complex.d (n + 1) n).hom.rTensor Q) := sorry

/-- Forget the termwise pure-projectivity condition on a pure projective resolution. -/
def toUniversallyExact (P : PureProjectiveResolution M) :
    UniversallyExactResolution M :=
  P.toUniversallyExactResolution

end PureProjectiveResolution

/-- Every module over a commutative ring admits a pure projective resolution. -/
@[stacks 0703]
theorem existsPureProjectiveResolution (M : ModuleCat.{u} A) :
    Nonempty (PureProjectiveResolution M) := sorry

end ModuleCat
