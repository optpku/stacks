module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Family
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.EtaleNeighborhood

@[expose] public section

universe u v

namespace AlgebraicGeometry.Scheme.SmoothCovering

/-- Every smooth covering family of a scheme admits an étale covering that refines it. -/
@[stacks 055V]
theorem exists_etaleRefinement
    {S : Scheme.{u}} {ι : Type v} {family : ι → CategoryTheory.Over S}
    (hfamily : SmoothCovering family) :
    ∃ 𝒱 : Scheme.Cover.{u} Scheme.etalePrecoverage S,
      CategoryTheory.SemiRepresentableFamily.Over.Refines 𝒱.toOverFamily
        (CategoryTheory.SemiRepresentableFamily.Over.ofArrows
          (fun i ↦ (family i).left) (fun i ↦ (family i).hom)) := sorry

end AlgebraicGeometry.Scheme.SmoothCovering
