/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.Noetherian
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module
public import stacks_project.Chap51.Lemma_51_8_3
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.OpenImmersion
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 51.8.4: let `X` be an integral locally Noetherian scheme and `U` a nonempty
open subscheme. If, at every `z ∉ U`, each associated prime `p` of the completion of
the local ring at `z` has `ringKrullDim (Ahat ⧸ p) ≥ 2`, then the pushforward of the
structure sheaf of `U` along `U.ι` is coherent. -/
@[stacks 0BK1] #check
  (AlgebraicGeometry.Scheme.Modules.pushforward_structureSheaf_isCoherent_of_completion_associatedPrimes :
    ∀ {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
      (U : X.Opens) [Nonempty U],
    (∀ z : X, z ∉ U →
      let Ahat := AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
        (X.presheaf.stalk z)
      ∀ p ∈ associatedPrimesOfModule Ahat Ahat,
        2 ≤ ringKrullDim (Ahat ⧸ p)) →
    ((pushforward U.ι).obj
      (SheafOfModules.unit (U : Scheme).ringCatSheaf)).IsCoherent)

end AlgebraicGeometry.Scheme.Modules
