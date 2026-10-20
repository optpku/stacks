module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite

@[expose] public section

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Sheafification identifies finite-support direct image with compact-support direct
image for a separated locally quasi-finite morphism. -/
def lowerShriekIso_separated {S T : Scheme.{u}} (h : S ⟶ T)
    [IsSeparated h] [LocallyQuasiFinite h] [LocallyOfFiniteType h] :
    lowerShriek h ≅ etaleLowerShriek h :=
  isoWhiskerRight (lowerShriekPresheafIso h)
      (presheafToSheaf T.smallEtaleTopology AddCommGrpCat.{u}) ≪≫
    associator (etaleLowerShriek h)
      (sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u})
      (presheafToSheaf T.smallEtaleTopology AddCommGrpCat.{u}) ≪≫
    isoWhiskerLeft (etaleLowerShriek h)
      (asIso (sheafificationAdjunction T.smallEtaleTopology AddCommGrpCat.{u}).counit) ≪≫
    rightUnitor (etaleLowerShriek h)

/-- The canonical comparison from finite-support to compact-support direct image
for a separated locally quasi-finite morphism. -/
def lowerShriekSeparatedComparison {S T : Scheme.{u}} (h : S ⟶ T)
    [IsSeparated h] [LocallyQuasiFinite h] [LocallyOfFiniteType h] :
    lowerShriek h ⟶ etaleLowerShriek h :=
  (lowerShriekIso_separated h).hom

/-- The separated finite-support comparison is invertible. -/
instance lowerShriekSeparatedComparison_isIso {S T : Scheme.{u}} (h : S ⟶ T)
    [IsSeparated h] [LocallyQuasiFinite h] [LocallyOfFiniteType h] :
    IsIso (lowerShriekSeparatedComparison h) :=
  (lowerShriekIso_separated h).isIso_hom

/-- The forward map of the separated identification is the canonical comparison. -/
theorem lowerShriekIso_separated_hom {S T : Scheme.{u}} (h : S ⟶ T)
    [IsSeparated h] [LocallyQuasiFinite h] [LocallyOfFiniteType h] :
    (lowerShriekIso_separated h).hom = lowerShriekSeparatedComparison h :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
