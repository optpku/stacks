module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat

/-!
# Descent of representable morphism properties along source covers

A property of morphisms of algebraic spaces that is fppf local on the target,
stable under base change, and τ-local on the source descends along a surjective
τ-cover of algebraic stacks, for τ in {étale, smooth, syntomic, fppf}.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom.has

/-- If `P` is fppf local on the target, stable under base change, and étale-local
on the source, then a morphism of algebraic stacks representable by algebraic
spaces has `P` as soon as it remains so after precomposition with a surjective
étale 1-morphism. -/
theorem of_comp_etale {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    [P.IsLocalAtSource AlgebraicSpace.etalePrecoverage]
    {f : X ⟶ Y} {g : Y ⟶ Z} [Etale f] [Surjective f]
    (hg : relativelyRepresentableByAlgebraicSpaces g) (hfg : has P (f ≫ g)) :
    has P g :=
  sorry

/-- If `P` is fppf local on the target, stable under base change, and smooth-local
on the source, then a morphism of algebraic stacks representable by algebraic
spaces has `P` as soon as it remains so after precomposition with a surjective
smooth 1-morphism. -/
theorem of_comp_smooth {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    [P.IsLocalAtSource (AlgebraicSpace.precoverage (@AlgebraicSpace.Smooth S))]
    {f : X ⟶ Y} {g : Y ⟶ Z} [Smooth f] [Surjective f]
    (hg : relativelyRepresentableByAlgebraicSpaces g) (hfg : has P (f ≫ g)) :
    has P g :=
  sorry

/-- If `P` is fppf local on the target, stable under base change, and
syntomic-local on the source, then a morphism of algebraic stacks representable
by algebraic spaces has `P` as soon as it remains so after precomposition with a
surjective syntomic 1-morphism. -/
theorem of_comp_syntomic {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    [P.IsLocalAtSource (AlgebraicSpace.precoverage (@AlgebraicSpace.Syntomic S))]
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : relativelyRepresentableByAlgebraicSpaces f)
    [Surjective f] (hτ : has (@AlgebraicSpace.Syntomic S) f)
    (hg : relativelyRepresentableByAlgebraicSpaces g) (hfg : has P (f ≫ g)) :
    has P g :=
  sorry

/-- If `P` is fppf local on the target, stable under base change, and fppf-local
on the source, then a morphism of algebraic stacks representable by algebraic
spaces has `P` as soon as it remains so after precomposition with a surjective
flat locally of finite presentation 1-morphism. -/
theorem of_comp_fppf {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    [P.IsLocalAtSource (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} {g : Y ⟶ Z} [Flat f] [Surjective f]
    (hfp : has (@AlgebraicSpace.LocallyOfFinitePresentation S) f)
    (hg : relativelyRepresentableByAlgebraicSpaces g) (hfg : has P (f ≫ g)) :
    has P g :=
  sorry

end AlgebraicGeometry.Groupoids.Hom.has
