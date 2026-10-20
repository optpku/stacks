module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteType.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

/- Lemma 35.7.1: a quasi-coherent scheme module whose pullbacks along an fpqc covering
family are finite type is itself finite type. -/
@[stacks 05AZ] #check
  (AlgebraicGeometry.Scheme.Modules.IsFiniteType.of_fpqcCovering :
    ∀ {X : Scheme.{u}} {ι : Type v} (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (family : ι → Over X), Scheme.FpqcCovering family →
      (∀ i : ι, ((Scheme.Modules.pullback (family i).hom).obj ℱ).IsFiniteType) →
      ℱ.IsFiniteType)
