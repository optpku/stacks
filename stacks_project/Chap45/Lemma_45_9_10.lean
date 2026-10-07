module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.WeilCohomology.MotivicRealization

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace WeilCohomology.MotivicRealization

/- Lemma 45.9.10: a field `k`, a characteristic-zero field `F`, and a ℚ-linear strong
monoidal realization `G` compatible with the Koszul symmetry and concentrating
`G(𝟙(1))` in degree `-2` determine the classical Weil data satisfying (A)(a), (A)(b),
(B), and (C), without asserting (A)(c) or (A)(d). -/
@[stacks 0FHK]
#check (WeilCohomology.MotivicRealization.existsClassicalCore_ofField :
    ∀ {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
      (G : ChowMotive k
        (fun _ ↦ AlgebraicGeometry.Correspondence.GradedCategory k) ⥤
          GradedObject ℤ (ModuleCat F))
      [G.Linear ℚ] [G.Monoidal],
      IsKoszulBraided G →
        (∀ i : ℤ, i ≠ -2 →
          IsZero ((G.obj (ChowMotive.tateTwist (SchemeOverField.point k) 1)) i)) →
        Nonempty (ClassicalCore G))

end WeilCohomology.MotivicRealization
