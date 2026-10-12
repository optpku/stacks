/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Fiber
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.20.6: for a locally finite type morphism of schemes, finite-type quasi-finiteness at
a point is equivalent to isolation in the fiber, to the closed-point and specialization criterion,
and to finite-type quasi-finiteness for every compatible affine presentation. -/
@[stacks 01TH] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.QuasiFiniteAt.fiberTFAE :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X),
      List.TFAE
        [ AlgebraicGeometry.Scheme.Hom.FiniteType.QuasiFiniteAt f x
        , IsOpen ({f.asFiber x} : Set (f.fiber (f x)))
        , f.asFiber x ∈ closedPoints (f.fiber (f x)) ∧
            ∀ x' : f.fiber (f x), x' ≠ f.asFiber x → ¬ Specializes x' (f.asFiber x)
        , ∀ ⦃U : X.Opens⦄, ∀ hU : IsAffineOpen U,
            ∀ ⦃V : S.Opens⦄, ∀ hV : IsAffineOpen V, ∀ e : U ≤ f ⁻¹ᵁ V,
              ∀ q : PrimeSpectrum (Γ(X, U)), hU.fromSpec q = x →
                (CommRingCat.Hom.hom (f.appLE V U e)).FiniteType ∧
                  (CommRingCat.Hom.hom (f.appLE V U e)).QuasiFiniteAt q.asIdeal
        ])
