/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.PureInjective.Copresentation
public import ReasLib.Algebra.Homology.CochainComplex.UniversallyExactCoresolution

@[expose] public section

open CategoryTheory

universe u v

namespace ModuleCat

variable {A : Type u} [CommRing A]

/-- A pure injective coresolution is a universally exact nonnegative cochain resolution
whose terms are pure injective. -/
structure PureInjectiveCoresolution (N : ModuleCat.{v} A)
    extends UniversallyExactCoresolution N where
  /-- Every term of the resolution is pure injective. -/
  pureInjective : ∀ n, (cocomplex.X n).PureInjective

namespace PureInjectiveCoresolution

variable {N : ModuleCat.{v} A}

/-- Construct a pure injective coresolution from its explicit cocomplex, augmentation,
termwise pure injectivity, and tensor-stable exactness properties. -/
def of (cocomplex : CochainComplex (ModuleCat.{v} A) ℕ) (ι : N ⟶ cocomplex.X 0)
    (ι_d : ι ≫ cocomplex.d 0 1 = 0)
    (pureInjective : ∀ n, (cocomplex.X n).PureInjective)
    (augmentationInjective :
      LinearMap.UniversallyInjective.{u, v, v, max u v} ι.hom)
    (augmentationExact : ∀ (Q : Type (max u v)) [AddCommGroup Q] [Module A Q],
      LinearMap.range (ι.hom.rTensor Q) =
        LinearMap.ker ((cocomplex.d 0 1).hom.rTensor Q))
    (successorExact : ∀ n (Q : Type (max u v)) [AddCommGroup Q] [Module A Q],
      LinearMap.range ((cocomplex.d n (n + 1)).hom.rTensor Q) =
        LinearMap.ker ((cocomplex.d (n + 1) (n + 2)).hom.rTensor Q)) :
    PureInjectiveCoresolution N :=
  { toUniversallyExactCoresolution :=
      UniversallyExactCoresolution.of cocomplex ι ι_d augmentationInjective
        augmentationExact successorExact
    pureInjective }

/-- Termwise pure injectivity and tensor-stable injectivity and exactness characterize a
pure injective coresolution. -/
theorem spec (I : PureInjectiveCoresolution N) :
    (∀ n, (I.cocomplex.X n).PureInjective) ∧
    LinearMap.UniversallyInjective.{u, v, v, max u v} I.ι.hom ∧
    (∀ (Q : Type (max u v)) [AddCommGroup Q] [Module A Q],
      LinearMap.range (I.ι.hom.rTensor Q) =
        LinearMap.ker ((I.cocomplex.d 0 1).hom.rTensor Q)) ∧
    ∀ n (Q : Type (max u v)) [AddCommGroup Q] [Module A Q],
      LinearMap.range ((I.cocomplex.d n (n + 1)).hom.rTensor Q) =
        LinearMap.ker ((I.cocomplex.d (n + 1) (n + 2)).hom.rTensor Q) := sorry

/-- Forget the termwise pure-injectivity condition on a pure injective coresolution. -/
def toUniversallyExact (I : PureInjectiveCoresolution N) :
    UniversallyExactCoresolution N :=
  I.toUniversallyExactCoresolution

end PureInjectiveCoresolution

/-- Every module over a commutative ring admits a pure injective coresolution. -/
theorem existsPureInjectiveResolution (M : ModuleCat.{v} A) :
    Nonempty (PureInjectiveCoresolution M) := sorry

end ModuleCat
