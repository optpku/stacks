module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Syntomic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiPrecoverage

/-!
# Comparisons with fppf coverings of algebraic spaces

Syntomic, smooth, étale, and Zariski covering families of algebraic spaces are
fppf covering families.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every syntomic covering family of algebraic spaces is an fppf covering. -/
theorem fppfCovering_of_syntomicCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} (h : SyntomicCovering family) :
    FppfCovering (fun i ↦ (family i).left) (fun i ↦ (family i).hom) := sorry

/-- Every smooth covering family of algebraic spaces is an fppf covering. -/
theorem fppfCovering_of_smoothCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} (h : SmoothCovering family) :
    FppfCovering (fun i ↦ (family i).left) (fun i ↦ (family i).hom) := sorry

/-- Every étale covering family of algebraic spaces is an fppf covering. -/
theorem fppfCovering_of_etaleCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} (h : EtaleCovering family) :
    FppfCovering (fun i ↦ (family i).left) (fun i ↦ (family i).hom) := sorry

/-- Every displayed Zariski covering family of algebraic spaces is an fppf covering. -/
theorem fppfCovering_of_zariskiPrecoverage {S : Scheme.{u}}
    {X : AlgebraicSpace S} {ι : Type v} {Xᵢ : ι → AlgebraicSpace S}
    {f : ∀ i, Xᵢ i ⟶ X} (h : Presieve.ofArrows Xᵢ f ∈ zariskiPrecoverage S X) :
    FppfCovering Xᵢ f := sorry

/-- Every displayed family in the étale precoverage is an fppf covering. -/
theorem fppfCovering_of_mem_etalePrecoverage {S : Scheme.{u}}
    {X : AlgebraicSpace S} {ι : Type v} {Xᵢ : ι → AlgebraicSpace S}
    {f : ∀ i, Xᵢ i ⟶ X} (h : Presieve.ofArrows Xᵢ f ∈ etalePrecoverage X) :
    FppfCovering Xᵢ f := sorry

end AlgebraicGeometry.AlgebraicSpace
