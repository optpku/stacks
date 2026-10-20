module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic

/-!
# Local surjectivity of fppf covering families

The canonical coproduct descent map of a small fppf covering of algebraic spaces
is locally surjective on the scheme fppf site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.FppfCovering

/-- The canonical coproduct descent map of a small fppf covering of algebraic
spaces over a scheme is locally surjective on the scheme fppf site, expressing
surjectivity of the induced map of sheaves. -/
@[stacks 0469]
instance instIsLocallySurjective_sheafCoproductDesc {S : Scheme.{u}} {ι : Type v}
    {X : AlgebraicSpace S} [Small.{u} ι] {X_i : ι → AlgebraicSpace S}
    {f : ∀ i, X_i i ⟶ X} [FppfCovering X_i f] :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sheafCoproductDesc X_i f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FppfCovering
