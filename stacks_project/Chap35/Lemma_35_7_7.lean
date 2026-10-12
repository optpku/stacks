/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.LocallyProjective.Fpqc
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

/- Lemma 35.7.7: a quasi-coherent scheme module whose pullbacks along an fpqc covering
family are locally projective is itself locally projective. -/
@[stacks 05JZ]
#check
  (AlgebraicGeometry.Scheme.Modules.IsLocallyProjective.of_fpqcCovering :
    ∀ {X : Scheme.{u}} {ι : Type v}
      (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (family : ι → Over X) (_ : Scheme.FpqcCovering family)
      (_ : ∀ i, Scheme.Modules.IsLocallyProjective
        ((Scheme.Modules.pullback (family i).hom).obj ℱ)),
      Scheme.Modules.IsLocallyProjective ℱ)
