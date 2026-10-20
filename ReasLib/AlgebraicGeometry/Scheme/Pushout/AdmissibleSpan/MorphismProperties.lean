module

public import ReasLib.AlgebraicGeometry.Scheme.Pushout.AdmissibleSpan.StructureMap
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Separated.Descent

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan

/-- The canonical morphism from `Y.left ⨿ X.left` to the pushout of an admissible
span is surjective. -/
instance instCoprodDescSurjective {S : Scheme.{u}} {Z X Y : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y) [IsAdmissibleSpan i j] :
    Surjective (coprod.desc (pushout.inr i.left j.left) (pushout.inl i.left j.left)) := sorry

/-- The pushout of an admissible span of separated schemes is separated. -/
instance instIsSeparated {S : Scheme.{u}} {Z X Y : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y) [IsAdmissibleSpan i j]
    [X.left.IsSeparated] [Y.left.IsSeparated] :
    (pushout i.left j.left).IsSeparated := sorry

/-- The canonical pushout structure morphism is separated when the two original
structure morphisms are separated. -/
instance instToBaseIsSeparated {S : Scheme.{u}} {Z X Y : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y) [IsAdmissibleSpan i j]
    [IsSeparated X.hom] [IsSeparated Y.hom] :
    IsSeparated (toBase i j) := sorry

/-- The pushout of an admissible span of quasi-separated schemes is quasi-separated. -/
instance instQuasiSeparatedSpace {S : Scheme.{u}} {Z X Y : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y) [IsAdmissibleSpan i j]
    [QuasiSeparatedSpace X.left] [QuasiSeparatedSpace Y.left] :
    QuasiSeparatedSpace (pushout i.left j.left : Scheme.{u}) := sorry

/-- The canonical pushout structure morphism is quasi-separated when the two original
structure morphisms are quasi-separated. -/
instance instToBaseQuasiSeparated {S : Scheme.{u}} {Z X Y : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y) [IsAdmissibleSpan i j]
    [QuasiSeparated X.hom] [QuasiSeparated Y.hom] :
    QuasiSeparated (toBase i j) := sorry

end AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan
