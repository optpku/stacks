/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.FiniteType.BasicOpenCover
public import ReasLib.AlgebraicGeometry.PrimeSpectrum.Notation
import StacksCheckRecall

@[expose] public section

universe u v w x

open PrimeSpectrum
open scoped PrimeSpectrum

/- Exercise 111.23.3: Suppose that `A → B` is a ring map, with
`Spec(A) = ⋃ D(f i)` and `Spec(B) = ⋃ D(g j)`. If every mixed localization
`A_(f i) → B_(f i g j)` is of finite type, then `A → B` is of finite type. -/
@[stacks 078T] #check (Algebra.FiniteType.of_basicOpen_cover :
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type w} {κ : Type x} (f : ι → A) (g : κ → B),
    (⨆ i, D(f i)) = ⊤ →
    (⨆ j, D(g j)) = ⊤ →
    (∀ i j, (Localization.awayMulMap (algebraMap A B) (f i) (g j)).FiniteType) →
    Algebra.FiniteType A B)
