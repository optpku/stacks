module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiPrecoverage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.OpenImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.Smooth

/-!
# Comparison of étale, Zariski, and smooth coverings of algebraic spaces

Every jointly surjective family of étale morphisms of algebraic spaces is a
smooth covering family, and therefore every Zariski covering family is a smooth
covering family.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every étale covering family of algebraic spaces is a smooth covering family. -/
theorem smoothCovering_of_etaleCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} :
    EtaleCovering family → SmoothCovering family :=
  sorry

/-- Every Zariski covering family of algebraic spaces, presented as an `Over`
family, is a smooth covering family. -/
theorem smoothCovering_of_zariskiPrecoverage {S : Scheme.{u}}
    {X : AlgebraicSpace S} {ι : Type v} {Xᵢ : ι → AlgebraicSpace S}
    {f : ∀ i, Xᵢ i ⟶ X} :
    Presieve.ofArrows Xᵢ f ∈ zariskiPrecoverage S X →
      SmoothCovering (fun i ↦ Over.mk (f i)) :=
  sorry

/-- A displayed family of étale morphisms whose images on points cover `|X|`
defines a smooth covering. -/
theorem smoothCovering_of_mem_etalePrecoverage {S : Scheme.{u}}
    {X : AlgebraicSpace S} {ι : Type v} {Xᵢ : ι → AlgebraicSpace S}
    {f : ∀ i, Xᵢ i ⟶ X} :
    Presieve.ofArrows Xᵢ f ∈ etalePrecoverage X →
      SmoothCovering (fun i ↦ Over.mk (f i)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
