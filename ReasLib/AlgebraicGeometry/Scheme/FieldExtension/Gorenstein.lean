module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Stalk.Local
public import ReasLib.RingTheory.Gorenstein.Local

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FieldExtension.Gorenstein

variable {k : Type u} [Field k]
variable {K : Type u} [Field K] [Algebra k K]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- Gorensteinness of corresponding stalks is equivalent for an essentially finite type
field-extension base change of a locally Noetherian scheme. -/
theorem stalk_iff_of_essFiniteType
    [IsLocallyNoetherian X] [Algebra.EssFiniteType k K]
    (x : X) (x' : FieldExtension.baseChange k K f)
    (hx : FieldExtension.toSource k K f x' = x) :
    IsGorensteinLocalRing (X.presheaf.stalk x) ↔
      IsGorensteinLocalRing ((FieldExtension.baseChange k K f).presheaf.stalk x') := sorry

/-- Gorensteinness of corresponding stalks is equivalent for an arbitrary field-extension
base change of a scheme locally of finite type over the base field. -/
theorem stalk_iff_of_locallyOfFiniteType
    [LocallyOfFiniteType f]
    (x : X) (x' : FieldExtension.baseChange k K f)
    (hx : FieldExtension.toSource k K f x' = x) :
    IsGorensteinLocalRing (X.presheaf.stalk x) ↔
      IsGorensteinLocalRing ((FieldExtension.baseChange k K f).presheaf.stalk x') := sorry

end AlgebraicGeometry.FieldExtension.Gorenstein
