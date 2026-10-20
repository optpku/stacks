module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.VanishingH1
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Universal injectivity of the canonical morphism to the spectrum of global sections

For a quasi-compact, absolutely quasi-separated algebraic space with vanishing
first cohomology on quasi-coherent modules, the absolute canonical morphism is
universally injective and each of its field-valued fibres has at most one point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every field-valued fibre of the absolute canonical morphism of a
quasi-compact, absolutely quasi-separated algebraic space with vanishing first
cohomology on quasi-coherent modules has at most one point. -/
instance subsingleton_points_toSpecAFiber {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X] {K : Type u} [Field K]
    (φ : globalSectionsRing X ⟶ CommRingCat.of K) :
    Subsingleton (Points (pullback (specMapSpecZ φ) (toSpecA X))) :=
  sorry

/-- The absolute canonical morphism of a quasi-compact, absolutely
quasi-separated algebraic space with vanishing first cohomology on
quasi-coherent modules is universally injective. -/
instance universallyInjective_toSpecA {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X] : UniversallyInjective (toSpecA X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
