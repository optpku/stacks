/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.NormalCrossings.NormalizationConfiguration
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom.FiberPower

universe u

/- Lemma 41.21.6: For a locally Noetherian scheme `X` and a closed subscheme `D`,
normal crossings are equivalent to `D` being reduced, its normalization being unramified,
and every positive pairwise-distinct normalization fibre power being regular and locally
complete intersection over `X`, with conormal sheaf of rank equal to the number of factors. -/
@[stacks 0CBR] #check
  (AlgebraicGeometry.isNormalCrossingsDivisor_iff_normalizationConfiguration :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (D : X.IdealSheafData),
      IsNormalCrossingsDivisor D ↔
        IsReduced D.subscheme ∧
          Unramified D.subscheme.normalizationTo ∧
            ∀ n : ℕ+,
              Scheme.Regular
                  (configurationOpen D.subscheme.normalizationTo n).toScheme ∧
                LocallyOfType RingHom.IsLocalCompleteIntersection
                  (configurationToBase D.subscheme.normalizationTo n ≫ D.subschemeι) ∧
                Scheme.Modules.IsFiniteLocallyFreeOfRank n
                  (Scheme.Hom.conormalSheaf
                    (configurationToBase D.subscheme.normalizationTo n ≫ D.subschemeι)))
