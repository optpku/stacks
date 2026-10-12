/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Extension
import StacksCheckRecall

/-!
# Lemma 31.28.3

Extension of invertible modules across a UFD complement.

@stack 0BD9
-/

@[expose] public section

universe u

/- Lemma 31.28.3: let `X` be a locally Noetherian scheme, let `U ⊆ X` be an open subscheme,
and let `ℒ` be an invertible module on `U`. If every stalk `𝒪_{X,x}` at a point of `X \ U`
is a unique factorization domain, then `ℒ` extends to an invertible module on `X`. -/
@[stacks 0BD9] #check
  (AlgebraicGeometry.Scheme.Modules.Invertible.exists_extension_of_stalks_uniqueFactorizationMonoid :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
      (U : X.Opens) (ℒ : U.toScheme.Modules)
      [AlgebraicGeometry.Scheme.Modules.Invertible ℒ]
      (_ : ∀ x : X, x ∉ (U : Set X) → UniqueFactorizationMonoid (X.presheaf.stalk x)),
      ∃ (ℒ' : X.Modules) (_ : AlgebraicGeometry.Scheme.Modules.Invertible ℒ'),
        Nonempty (ℒ ≅ (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj ℒ'))
