module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Pushforward

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicCycle

/- Lemma 42.12.2: for proper morphisms of schemes locally of finite type over `S`, successive
pushforward on degree-`k` cycles equals pushforward along the composite. -/
@[stacks 02R5] #check
  (AlgebraicGeometry.AlgebraicCycle.map_comp_on_dimensionSubgroup_of_proper :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y Z : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper f.left] [IsProper g.left] (k : ℤ),
    (fun c : dimensionSubgroup (X.hom.relativeDimensionFunction δ) k ↦
      map g.left (Y.hom.relativeDimensionFunction δ) (Z.hom.relativeDimensionFunction δ)
        (map f.left (X.hom.relativeDimensionFunction δ)
          (Y.hom.relativeDimensionFunction δ) (c : AlgebraicCycle X.left ℤ))) =
      fun c : dimensionSubgroup (X.hom.relativeDimensionFunction δ) k ↦
        map (f.left ≫ g.left) (X.hom.relativeDimensionFunction δ)
          (Z.hom.relativeDimensionFunction δ) (c : AlgebraicCycle X.left ℤ))

end AlgebraicGeometry.AlgebraicCycle
