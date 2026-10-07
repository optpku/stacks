module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Ph.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

/- Lemma 37.48.7: an fppf covering family of schemes is a ph covering family. -/
@[stacks 0DBT] #check
  (AlgebraicGeometry.Scheme.FppfCovering.phCovering :
    ∀ {T : Scheme.{u}} {ι : Type v} {family : ι → CategoryTheory.Over T},
      AlgebraicGeometry.Scheme.FppfCovering family →
        AlgebraicGeometry.PhCovering (fun i ↦ (family i).left) (fun i ↦ (family i).hom))
