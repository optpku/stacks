module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Fiber
import StacksCheckRecall

universe u

open AlgebraicGeometry

/- Lemma 29.30.11: a flat, locally finitely presented morphism whose residue-field fibers are
local complete intersections is syntomic. -/
@[stacks 01UF] #check
  (AlgebraicGeometry.Syntomic.of_syntomic_fiberToSpecResidueField :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      [Flat f] → [LocallyOfFinitePresentation f] →
        (∀ s : S,
          IsLocalCompleteIntersectionOver (S.residueField s)
            (f.fiberToSpecResidueField s)) →
        Syntomic f)
