/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.OpenImmersion
import StacksCheckRecall

universe u

open IsLocalRing

@[expose] public section

namespace AlgebraicGeometry.Scheme.Modules

/- Proposition 51.8.7 (Kollár): for a coherent module `ℱ` on an open subscheme
`U` of a locally Noetherian scheme `X`, the pushforward `(pushforward U.ι).obj ℱ`
is coherent exactly when every associated point of `ℱ`, every point of its reduced
point closure outside `U`, and every associated prime of the completed local ring
at that point satisfy the dimension bound `2 ≤ ringKrullDim (Ahat ⧸ p)`. -/
@[stacks 0BK3] #check
  (AlgebraicGeometry.Scheme.Modules.pushforward_obj_isCoherent_iff_completion_associatedPrimes :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens)
      (ℱ : (U : Scheme).Modules) [ℱ.IsCoherent],
    ((pushforward U.ι).obj ℱ).IsCoherent ↔
      ∀ x : U, x ∈ ℱ.associatedPoints →
        ∀ z : PointClosure.scheme (U.ι x),
          PointClosure.ι (U.ι x) z ∉ U →
            let Ahat :=
              AdicCompletion
                (maximalIdeal ((PointClosure.scheme (U.ι x)).presheaf.stalk z))
                ((PointClosure.scheme (U.ι x)).presheaf.stalk z)
            ∀ p ∈ associatedPrimesOfModule Ahat Ahat,
              2 ≤ ringKrullDim (Ahat ⧸ p))

end AlgebraicGeometry.Scheme.Modules
