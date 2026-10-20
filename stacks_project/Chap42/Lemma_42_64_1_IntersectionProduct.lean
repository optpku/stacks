module

public import ReasLib.AlgebraicGeometry.ChowGroup.Dedekind.Intersection

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.Dedekind

/- The constant-rank intersection product on total relative Chow homology. -/
#check (AlgebraicGeometry.ChowGroup.Dedekind.intersectionProduct :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    {X Y Z : Over S}
    [LocallyOfFiniteType X.hom] [Smooth X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left]
    (e : Scheme.Modules.dual (normalSheaf (diagonal X).left) ≅
      conormalSheaf (diagonal X).left)
    (D : DiagonalSpecialization δ X e) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (alpha : Total δ Y) (beta : Total δ Z),
    Total δ (pullback fY fZ))

end AlgebraicGeometry.ChowGroup.Dedekind
