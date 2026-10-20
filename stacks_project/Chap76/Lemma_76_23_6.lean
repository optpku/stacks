module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.Locus.BaseChange
import StacksCheckRecall

/-!
# Openness of the pointwise-flatness locus of a morphism of algebraic spaces

In a triangle `X ⟶ Y ⟶ Z` of algebraic spaces over a scheme `S`, if `X` is
locally of finite presentation and flat over `Z` and `Y` is locally of finite
type over `Z`, then the locus of points of `X` at which `X` is flat over `Y`
is open, and it commutes with arbitrary base change of `Z`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.23.6 (1): Let `S` be a scheme. Let `f : X ⟶ Y` and `h : Y ⟶ Z` be
morphisms of algebraic spaces over `S`. Assume `X` is locally of finite
presentation over `Z`, `X` is flat over `Z`, and `Y` is locally of finite type
over `Z`. Then `{x | FlatAt f x}` is open in `Points X`. -/
@[stacks 05X3]
#check (AlgebraicGeometry.AlgebraicSpace.isOpen_flatAt :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (h : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ h)]
    [Flat (f ≫ h)] [LocallyOfFiniteType h],
    IsOpen {x | FlatAt f x})

/- Lemma 76.23.6 (2): Let `S` be a scheme. Let `f : X ⟶ Y` and `h : Y ⟶ Z` be
morphisms of algebraic spaces over `S`. Assume `X` is locally of finite
presentation over `Z`, `X` is flat over `Z`, and `Y` is locally of finite type
over `Z`. For a morphism `g : Z' ⟶ Z` of algebraic spaces over `S`, the set
`{x' | FlatAt (overBaseChange f h g) x'}` is the inverse image of
`{x | FlatAt f x}` under `Points.map (pullback.fst (f ≫ h) g)`. -/
@[stacks 05X3]
#check (AlgebraicGeometry.AlgebraicSpace.flatAt_baseChange_eq_preimage :
    ∀ {S : Scheme.{u}}
    {X Y Z Z' : AlgebraicSpace S} (f : X ⟶ Y) (h : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ h)] [Flat (f ≫ h)]
    [LocallyOfFiniteType h],
    {x' | FlatAt (overBaseChange f h g) x'} =
      Points.map (pullback.fst (f ≫ h) g) ⁻¹' {x | FlatAt f x})

/- A point of `Points (pullback (f ≫ h) g)` lies in the pointwise flatness
locus of `overBaseChange f h g` if and only if its image under
`Points.map (pullback.fst (f ≫ h) g)` lies in `{x | FlatAt f x}`. -/
#check (AlgebraicGeometry.AlgebraicSpace.mem_flatAt_baseChange_eq_preimage :
    ∀ {S : Scheme.{u}}
    {X Y Z Z' : AlgebraicSpace S} (f : X ⟶ Y) (h : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ h)] [Flat (f ≫ h)]
    [LocallyOfFiniteType h] (x' : Points (pullback (f ≫ h) g)),
    FlatAt (overBaseChange f h g) x' ↔
      Points.map (pullback.fst (f ≫ h) g) x' ∈ {x | FlatAt f x})

end AlgebraicGeometry.AlgebraicSpace
