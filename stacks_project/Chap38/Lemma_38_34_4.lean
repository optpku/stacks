module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.H.Comparison
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 38.34.4: over a locally Noetherian scheme, h covering families are
exactly ph covering families. -/
@[stacks 0H45] #check
  (AlgebraicGeometry.Scheme.hCovering_iff_phCovering :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
      {ι : Type v} (family : ι → CategoryTheory.Over X),
    AlgebraicGeometry.Scheme.HCovering family ↔
      AlgebraicGeometry.PhCovering
        (fun i ↦ (family i).left) (fun i ↦ (family i).hom))
