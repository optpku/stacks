/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Extension
import StacksCheckRecall

universe u

/- Lemma 31.28.2: let `X` be a locally Noetherian scheme, let `U ⊆ X` be an open subscheme,
 and let `D ⊆ U` be an effective Cartier divisor. If every stalk `𝒪_{X,x}` at a point
of `X \ U` is a unique factorization domain, then `D` extends to an effective Cartier divisor
`D' ⊆ X`; equivalently, the restriction of `D'` to `U` is `D`. -/
@[stacks 0BD8] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.exists_extension_of_stalks_uniqueFactorizationMonoid :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
      (U : X.Opens) (D : U.toScheme.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
      (_ : ∀ x : X, x ∉ (U : Set X) → UniqueFactorizationMonoid (X.presheaf.stalk x)),
      ∃ D' : X.IdealSheafData,
        AlgebraicGeometry.IsEffectiveCartierDivisor D'.subschemeι ∧ D = D'.comap U.ι)
