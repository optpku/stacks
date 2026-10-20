module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CohomologicalDimension.FieldExtension
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 59.95.4: if `L / K` is a field extension, then
`cohomologicalDimension (Spec (CommRingCat.of L)) ≤
  cohomologicalDimension (Spec (CommRingCat.of K)) +
    Cardinal.toENat (Algebra.trdeg K L)`. Infinite transcendence degree is read as `⊤`. -/
@[stacks 0F0T] #check (AlgebraicGeometry.Scheme.cohomologicalDimension_le_add_trdeg :
  ∀ {K : Type u} [Field K]
    [HasSheafify (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u})]
    {L : Type u} [Field L] [Algebra K L]
    [HasSheafify (Spec (CommRingCat.of L)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (CommRingCat.of L)).smallEtaleTopology AddCommGrpCat.{u})],
    Scheme.cohomologicalDimension (Spec (CommRingCat.of L)) ≤
      Scheme.cohomologicalDimension (Spec (CommRingCat.of K)) +
        id (α := WithTop ℕ) (Cardinal.toENat (Algebra.trdeg K L)))

/- Vanishing bound form of the field-extension comparison for cohomological dimension. -/
#check (AlgebraicGeometry.Scheme.cohomologicalDimensionBound_add_trdeg :
  ∀ {K : Type u} [Field K]
    [HasSheafify (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u})]
    {L : Type u} [Field L] [Algebra K L]
    [HasSheafify (Spec (CommRingCat.of L)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (CommRingCat.of L)).smallEtaleTopology AddCommGrpCat.{u})],
    Scheme.cohomologicalDimensionBound (Spec (CommRingCat.of L))
      (Scheme.cohomologicalDimension (Spec (CommRingCat.of K)) +
        id (α := WithTop ℕ) (Cardinal.toENat (Algebra.trdeg K L))))

end
