module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.IrreducibleComponents

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory CommRingCat
open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

noncomputable section

section

/- Lemma 33.8.8 (038H): for a field extension `k' / k` with `k` separably closed, the source
projection `X_{k'} ⟶ X` induces the canonical equivalence on irreducible components. -/
@[stacks 038H]
#check (@AlgebraicGeometry.FieldExtension.Irreducible.componentsEquiv_of_isSepClosed :
  ∀ (k K : Type u) [Field k] [IsSepClosed k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)),
    irreducibleComponents (FieldExtension.baseChange k K f) ≃ irreducibleComponents X)

#check (@AlgebraicGeometry.FieldExtension.Irreducible.coe_componentsEquiv_apply :
  ∀ (k K : Type u) [Field k] [IsSepClosed k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (T : irreducibleComponents (FieldExtension.baseChange k K f)),
    ((FieldExtension.Irreducible.componentsEquiv_of_isSepClosed k K f T :
        irreducibleComponents X) : Set X) =
      (FieldExtension.toSource k K f).base ''
        (T : Set (FieldExtension.baseChange k K f)))

end

end

end AlgebraicGeometry.Scheme.Hom
