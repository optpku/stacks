module

public import Mathlib.CategoryTheory.ObjectProperty.InheritedFromHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Reducedness is inherited from the target of a smooth morphism of algebraic spaces. -/
@[stacks 0GB3]
instance isReduced_inheritedFromTarget {S : Scheme.{u}} :
    InheritedFromTarget (@IsReduced S : ObjectProperty (AlgebraicSpace S))
      (@Smooth S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- Reducedness is inherited from the source of a surjective smooth morphism of
algebraic spaces. -/
@[stacks 0GB3]
instance isReduced_inheritedFromSource {S : Scheme.{u}} :
    InheritedFromSource (@IsReduced S : ObjectProperty (AlgebraicSpace S))
      ((@Smooth S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Surjective S : MorphismProperty (AlgebraicSpace S))) := sorry

/-- If `f : X ⟶ Y` is a smooth morphism of algebraic spaces and `Y` is reduced,
then `X` is reduced. -/
theorem IsReduced.of_smooth {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Smooth f] [IsReduced Y] : IsReduced X :=
  of_hom_of_target (P := @IsReduced S) (Q := @Smooth S) f inferInstance inferInstance

/-- If `f : X ⟶ Y` is a surjective smooth morphism of algebraic spaces and `X` is
reduced, then `Y` is reduced. -/
theorem IsReduced.of_smooth_surjective {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Smooth f] [Surjective f] [IsReduced X] : IsReduced Y :=
  of_hom_of_source (P := @IsReduced S) (Q := (@Smooth S) ⊓ (@Surjective S)) f
    ⟨inferInstance, inferInstance⟩ inferInstance

end AlgebraicGeometry.AlgebraicSpace
