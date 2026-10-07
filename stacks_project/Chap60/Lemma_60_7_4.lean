module

public import stacks_project.Chap60.Definition_60_7_2
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import stacks_project.Chap60.Lemma_60_7_4_Category
public import stacks_project.Chap60.Lemma_60_7_4_Comparison
import Mathlib.Tactic.CrossRefAttribute

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

@[expose] public section

universe u

variable {S T T' : DividedPowerScheme.{u}}

/-- Lemma 60.7.4: for morphisms of divided-power schemes with common target,
there is a divided-power pullback whose underlying scheme maps by a closed
immersion to the ordinary pullback and whose induced zero-fibre comparison is
an isomorphism. -/
@[stacks 07ME]
theorem DividedPowerScheme.existsPullback
    (f : DividedPowerScheme.Hom T S) (f' : DividedPowerScheme.Hom T' S) :
    ∃ (T'' : DividedPowerScheme.{u})
      (g : DividedPowerScheme.Hom T'' T)
      (g' : DividedPowerScheme.Hom T'' T')
      (h : @CategoryTheory.IsPullback DividedPowerScheme _ T'' T T' S g g' f f'),
      IsClosedImmersion
          (DividedPowerScheme.Pullback.baseComparison f f' g g' h) ∧
        IsIso
          (DividedPowerScheme.Pullback.zeroFiberComparison f f' g g' h) := sorry
