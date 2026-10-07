module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.Correspondence

@[expose] public section

universe u v

/- Proposition 45.11.6 -/
@[stacks 0GIJ]
#check (WeilCohomology.weilTheoryCorrespondence :
    ∀ {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F],
      ∃ e : WeilCohomology.SchemeClassicalTheory.Object k F ≃
          WeilCohomology.MotivicRealization.Admissible k F,
        ∀ T, T.IsWeil ↔ (e T).IsWeil)
