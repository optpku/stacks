/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Counterexample
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/- Remark 59.77.2: there can be a perfect derived `𝒪_X`-module with no global
representative that is both bounded and termwise locally free. This contrasts with
`D_ctf(X_étale, Λ)`: the following Lemma 59.77.3 gives its positive global-model
statement, so the same failure does not occur for `D_ctf` on a Noetherian scheme. -/
@[stacks 03TS] #check (AlgebraicGeometry.Scheme.existsPerfectWithoutGlobalLocallyFreeModel :
    ∃ (X : Scheme.{u}) (K : RingedSpace.ModuleDerived X.toRingedSpace),
      RingedSpace.ModuleDerived.IsPerfect K ∧
        ¬ ∃ P : CochainComplex X.toRingedSpace.Modules ℤ,
          IsIsomorphic (DerivedCategory.Q.obj P) K ∧
            CochainComplex.bounded X.toRingedSpace.Modules P ∧
              ∀ i : ℤ, (P.X i).IsLocallyFree)

end AlgebraicGeometry.Scheme
