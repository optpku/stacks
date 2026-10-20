module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Gorenstein
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FieldExtension.Gorenstein

/- Lemma 48.25.1 (1) -/
@[stacks 0C03] #check
  (AlgebraicGeometry.FieldExtension.Gorenstein.stalk_iff_of_essFiniteType :
    ∀ {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
      [IsLocallyNoetherian X] [Algebra.EssFiniteType k K]
      (x : X) (x' : FieldExtension.baseChange k K f)
      (hx : FieldExtension.toSource k K f x' = x),
      IsGorensteinLocalRing (X.presheaf.stalk x) ↔
        IsGorensteinLocalRing ((FieldExtension.baseChange k K f).presheaf.stalk x'))

/- Lemma 48.25.1 (2) -/
@[stacks 0C03] #check
  (AlgebraicGeometry.FieldExtension.Gorenstein.stalk_iff_of_locallyOfFiniteType :
    ∀ {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
      (x : X) (x' : FieldExtension.baseChange k K f)
      (hx : FieldExtension.toSource k K f x' = x),
      IsGorensteinLocalRing (X.presheaf.stalk x) ↔
        IsGorensteinLocalRing ((FieldExtension.baseChange k K f).presheaf.stalk x'))

end AlgebraicGeometry.FieldExtension.Gorenstein
