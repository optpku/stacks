module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

/- Lemma 35.7.6: a quasi-coherent scheme module whose pullbacks along an fpqc covering
family are finite locally free is itself finite locally free. -/
@[stacks 05B2] #check
  (AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree.of_fpqcCovering :
    ∀ {X : Scheme.{u}} {ι : Type v}
      (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (family : ι → Over X), Scheme.FpqcCovering family →
      (∀ i : ι,
        ((Scheme.Modules.pullback (family i).hom).obj ℱ).IsFiniteLocallyFree) →
      ℱ.IsFiniteLocallyFree)
