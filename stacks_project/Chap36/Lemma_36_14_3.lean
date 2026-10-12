/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PerfectApproximation.Restriction

@[expose] public section

universe u

/- Lemma 36.14.3: let `T` be a closed subset of a scheme `X`, let `U ⊆ X` be an open
subscheme containing `T`, let `E` have quasicoherent cohomology, and let `m : ℤ`. If
approximation holds for `(T, E|_U, m)` over `U` and every `H^i(E)` with `m ≤ i` is supported
on `T`, then approximation holds for `(T, E, m)` over `X`. -/
@[stacks 08EP] #check
  (AlgebraicGeometry.Scheme.HasPerfectApproximation.of_restrict :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (T : TopologicalSpace.Closeds X) (U : X.Opens)
    (hTU : (T : Set X) ⊆ (U : Set X))
    (E : CategoryTheory.DerivedCategory.CohomologyIn
      (AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) (m : ℤ)
    (hU : @AlgebraicGeometry.Scheme.HasPerfectApproximation U.toScheme
      (T.preimage continuous_subtype_val)
      ((AlgebraicGeometry.Scheme.DerivedQCoh.OpenImmersion.pullback U.ι).obj E) m)
    (hE : ∀ i : ℤ, m ≤ i →
      AlgebraicGeometry.RingedSpace.moduleSupportedOn (T : Set X)
        (AlgebraicGeometry.RingedSpace.ModuleDerived.cohomologySheaf E.obj i)),
      AlgebraicGeometry.Scheme.HasPerfectApproximation T E m)
