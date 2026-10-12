/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.Vanishing

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpace.ModuleDerived
open SheafOfModules.ClosedSubset.SupportedDerived

noncomputable section

universe u

/- Lemma 36.6.8: if the closed subset `T` of a scheme `X` is locally the common
zero locus of at most `c` sections of `𝒪_X`, then the local-cohomology sheaf
`𝓗^i_T(ℱ)` vanishes for `c < i` and every quasi-coherent `𝒪_X`-module `ℱ`. -/
@[stacks 0G7N] #check
  (AlgebraicGeometry.ClosedSubset.localCohomologySheaf_isZero_of_locallyCutOutBy :
    ∀ (X : Scheme.{u}) (T : TopologicalSpace.Closeds X) (c : ℕ)
      (hT : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
        ∃ d : ℕ, d ≤ c ∧ ∃ f : Fin d → Γ(X, U),
          (T : Set X) ∩ (U : Set X) = X.zeroLocus (Set.range f) ∩ (U : Set X))
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℤ) (hi : (c : ℤ) < i),
      IsZero
        (cohomologySheaf
          ((coreflector X.toRingedSpace.ringCatSheaf T ⋙
              inclusion X.toRingedSpace.ringCatSheaf T).obj
            ((ModuleCech.moduleToDerived X).obj ℱ)) i))

end
