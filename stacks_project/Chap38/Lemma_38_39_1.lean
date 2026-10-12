/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Colimit.VectorBundle
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 38.39.1: for a quasi-compact and quasi-separated scheme `S` of prime
characteristic `p`, the Frobenius colimit of finite locally free `𝒪_S`-modules
is equivalent to the category of finite locally free modules over the
Frobenius-colimit structure sheaf. -/
@[stacks 0EXB]
#check (AlgebraicGeometry.Scheme.FrobeniusColimit.vectorBundlesEquiv :
  ∀ (p : ℕ) [Fact p.Prime] (S : AlgebraicGeometry.Scheme.{u}) [S.IsCharP p]
    [CompactSpace S] [QuasiSeparatedSpace S],
    Nonempty
      (AlgebraicGeometry.Scheme.FrobeniusColimit.vectorBundleColimit p S ≌
        AlgebraicGeometry.Scheme.FrobeniusColimit.finiteLocallyFreeModules p S))
