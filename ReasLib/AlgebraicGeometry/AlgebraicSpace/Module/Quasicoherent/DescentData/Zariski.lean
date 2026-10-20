module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiPrecoverage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.DescentData.Canonical

/-!
# Zariski descent of quasi-coherent modules on algebraic spaces

Quasi-coherent modules on algebraic spaces satisfy effective descent along
Zariski covering families.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

variable {I : Type v} {S : Scheme.{u}} {X : AlgebraicSpace S}

namespace DescentData

/-- Every quasi-coherent descent datum along a Zariski covering family of
algebraic spaces is effective. -/
theorem isEffective_of_zariskiCovering (Xᵢ : I → AlgebraicSpace S)
    (f : ∀ i, Xᵢ i ⟶ X)
    (h𝒰 : Presieve.ofArrows Xᵢ f ∈ zariskiPrecoverage S X)
    (D : DescentData Xᵢ f) : D.IsEffective := sorry

end DescentData

namespace canonicalFunctor

/-- The canonical functor from quasi-coherent modules to descent data along a
Zariski covering family of algebraic spaces is fully faithful. -/
theorem fullyFaithful_of_zariskiCovering (Xᵢ : I → AlgebraicSpace S)
    (f : ∀ i, Xᵢ i ⟶ X)
    (h𝒰 : Presieve.ofArrows Xᵢ f ∈ zariskiPrecoverage S X) :
    Nonempty (canonicalFunctor Xᵢ f).FullyFaithful := sorry

end canonicalFunctor

end AlgebraicGeometry.AlgebraicSpace.QCoh
