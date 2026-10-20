module

public import ReasLib.AlgebraicGeometry.ChowGroup.Dedekind.ExteriorProduct

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set

noncomputable section

universe u

namespace AlgebraicGeometry

namespace CycleGroup.Dedekind

/-- The cycle-level exterior product over a locally Dedekind base as a biadditive pairing. -/
abbrev exteriorProductPairing
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) :=
  ExteriorProduct.cyclePairing δ h_delta X Y n m

end CycleGroup.Dedekind

namespace ChowGroup.Dedekind

/-- The degreewise Chow exterior product over a locally Dedekind base as a biadditive pairing. -/
abbrev exteriorProductPairing
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) :=
  ExteriorProduct.pairing δ h_delta X Y n m

end ChowGroup.Dedekind

end AlgebraicGeometry
