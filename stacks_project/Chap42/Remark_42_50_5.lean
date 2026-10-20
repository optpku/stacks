module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.LocalizedChern.Extension

open CategoryTheory AlgebraicGeometry

universe u

/- Remark 42.50.5: In Situation 42.50.1 it would have been more natural to replace
assumption (3) with the assumption that the Chern classes of E are defined.
Combining Lemmas 42.50.2 and 42.50.4 with the envelope descent of Lemma 42.35.6
extends the definition to this slightly more general case. The unique-existence
statement records this extendibility for both restriction modes; the source
defers an explicit construction until it is needed. -/
@[stacks 0GUK] #check (AlgebraicGeometry.LocalizedChern.existsUnique_of_isDefined :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (mode : LocalizedChern.RestrictionBehavior)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (offCenter : LocalizedChern.OffCenterCondition i E p mode)
    (hDefined : ChernClass.Derived.IsDefined E),
    ∃! c : BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ),
      LocalizedChern.IsLocalizedClass i classes E p mode c)
