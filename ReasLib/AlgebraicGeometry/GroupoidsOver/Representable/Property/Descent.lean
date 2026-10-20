module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.CategoryTheory.Fibered.Groupoids.GerbeMorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property

/-!
# Descent of representable morphisms having a morphism property

Properties of algebraic-space morphisms stable under base change and fppf local
on the target descend along fppf-locally essentially surjective morphisms of
groupoid fibrations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Let `P` be a property of algebraic-space morphisms stable under base change
and fppf local on the target. If `f` is representable by algebraic spaces and
`g` is fppf-locally essentially surjective, then `f` has `P` whenever its
canonical base change along `g` has `P`. -/
@[stacks 045D]
theorem has.of_pullback_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    (f : X ⟶ Y) (g : Z ⟶ Y) (hf : relativelyRepresentableByAlgebraicSpaces f)
    (hg : LocallyEssentiallySurjective (Scheme.fppfTopology.over S) g)
    (hf' : has P (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f)) :
    has P f := sorry

end AlgebraicGeometry.Groupoids.Hom
