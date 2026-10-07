module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import stacks_project.Chap87.Definition_87_11_1_Representable

/-!
# Composition of morphisms representable by algebraic spaces

On the chosen big fppf site `(Sch/S)_fppf`, representability by algebraic
spaces is stable under composition of sheaf morphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty ChosenBigFppfSite

universe u v

namespace AlgebraicGeometry.ChosenBigFppfSite

/-- Representability by algebraic spaces is stable under composition of
morphisms of sheaves on `(Sch/S)_fppf`. -/
instance representableByAlgebraicSpaces.isStableUnderComposition
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))] :
    IsStableUnderComposition
      (fun {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) ↦
        representableByAlgebraicSpaces f) :=
  sorry

/-- If `f : X ⟶ Y` and `g : Y ⟶ Z` are representable by algebraic spaces, then
so is the composite `f ≫ g`. -/
theorem representableByAlgebraicSpaces.comp_mem
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : representableByAlgebraicSpaces f) (hg : representableByAlgebraicSpaces g) :
    representableByAlgebraicSpaces (f ≫ g) :=
  sorry

end AlgebraicGeometry.ChosenBigFppfSite
