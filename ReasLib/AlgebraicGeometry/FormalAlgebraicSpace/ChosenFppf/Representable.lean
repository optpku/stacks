module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Basic

/-!
# Representability of morphisms to formal algebraic spaces

Morphisms from algebraic-space sheaves to formal-algebraic-space sheaves on a
chosen big fppf site are representable by algebraic spaces.
A sheaf admitting a morphism representable by algebraic spaces to a formal
algebraic space is itself a formal algebraic space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry.ChosenBigFppfSite

/-- A morphism from an algebraic-space sheaf to a formal-algebraic-space sheaf
on a chosen big fppf site is representable by algebraic spaces. -/
theorem representableByAlgebraicSpaces.of_isAlgebraicSpace
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y) :
    representableByAlgebraicSpaces f :=
  sorry

/-- The fibre product of a morphism from an algebraic space to a formal
algebraic space along a sheafified representable is an algebraic space. -/
instance instIsAlgebraicSpace_pullback_hom
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y)
    {U : 𝒮.bigSite S} (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ Y) :
    IsAlgebraicSpace (pullback ξ f) :=
  representableByAlgebraicSpaces.of_isAlgebraicSpace f ξ

/-- For morphisms of formal algebraic spaces on a chosen big fppf site,
representability of a composite by algebraic spaces implies representability
of its first morphism by algebraic spaces. -/
theorem representableByAlgebraicSpaces.of_comp
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : representableByAlgebraicSpaces (f ≫ g)) :
    representableByAlgebraicSpaces f :=
  sorry

end AlgebraicGeometry.ChosenBigFppfSite

namespace AlgebraicGeometry.IsFormalAlgebraicSpace

/-- A sheaf admitting a morphism to an affine formal algebraic space that is
representable by algebraic spaces is a formal algebraic space. -/
theorem of_representableByAlgebraicSpaces
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace Y] {f : X ⟶ Y}
    (hf : representableByAlgebraicSpaces f) :
    IsFormalAlgebraicSpace X :=
  sorry

/-- A sheaf admitting a morphism to a formal algebraic space that is
representable by algebraic spaces is a formal algebraic space. -/
theorem of_representableByAlgebraicSpaces_of_formal
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace Y] {f : X ⟶ Y}
    (hf : representableByAlgebraicSpaces f) :
    IsFormalAlgebraicSpace X :=
  sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace
