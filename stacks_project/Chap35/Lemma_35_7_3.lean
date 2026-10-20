module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

/- Lemma 35.7.3: a quasi-coherent scheme module whose pullbacks along an fpqc covering
family are finitely presented is itself finitely presented. -/
@[stacks 05B0] #check
  (AlgebraicGeometry.Scheme.Modules.IsFinitePresentation.of_fpqcCovering :
    ∀ {X : Scheme.{u}} {ι : Type v} (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (family : ι → Over X), Scheme.FpqcCovering family →
      (∀ i : ι,
        ((Scheme.Modules.pullback (family i).hom).obj ℱ).IsFinitePresentation) →
      ℱ.IsFinitePresentation)
