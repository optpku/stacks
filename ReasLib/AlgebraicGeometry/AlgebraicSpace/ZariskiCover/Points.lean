module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-! # Zariski coverings detected on points -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u w

namespace AlgebraicGeometry.AlgebraicSpace

/-- A small family of open immersions is a Zariski covering if and only if its point images
cover the ambient point space. -/
theorem isZariskiCover_iff_iUnion_pointsSet {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : Type w} [small : Small.{u} I] (Fi : I → AlgebraicSpace S) (ι : ∀ i, Fi i ⟶ X)
    [h_open : ∀ i, IsOpenImmersion (ι i)] :
    IsZariskiCover X Fi ι ↔ ⋃ i, Set.range (Points.map (ι i)) = Set.univ :=
  sorry

namespace ZariskiCover

/-- The point images of the members of a Zariski covering cover the ambient point space. -/
theorem iUnion_pointsSet {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover X) :
    ⋃ i, Set.range (Points.map (𝒰.f i)) = Set.univ :=
  (isZariskiCover_iff_iUnion_pointsSet (small := 𝒰.small) 𝒰.X 𝒰.f
    (h_open := 𝒰.isOpenImmersion)).mp
      ⟨fun i ↦ (𝒰.isOpenImmersion i).presheaf, 𝒰.covers⟩

end ZariskiCover

end AlgebraicGeometry.AlgebraicSpace
