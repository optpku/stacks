module

public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiAffine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

/-!
# Closed-immersion factorizations through morphisms of finite presentation

A locally of finite type quasi-affine morphism of algebraic spaces, with
quasi-compact quasi-separated target, factors as a closed immersion followed by
a morphism of finite presentation.

A locally of finite type morphism of algebraic spaces, with quasi-compact
quasi-separated source and target, factors as a closed immersion followed by
a morphism of finite presentation.

A finite type separated morphism of algebraic spaces, with quasi-compact
quasi-separated target, factors as a closed immersion followed by a separated
morphism of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally of finite type quasi-affine morphism of algebraic spaces over a
scheme, with quasi-compact quasi-separated target, factors as a closed immersion
followed by a morphism of finite presentation. -/
theorem exists_closedImmersion_factorization_of_locallyOfFiniteType_quasiAffine
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiAffine f]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y] :
    (MorphismProperty.comp
      (@IsClosedImmersion S : MorphismProperty (AlgebraicSpace S))
      (@FinitePresentation S : MorphismProperty (AlgebraicSpace S))) f :=
  sorry

/-- A locally of finite type morphism of algebraic spaces over a scheme, with
quasi-compact quasi-separated source and target, factors as a closed immersion
followed by a morphism of finite presentation. -/
theorem exists_closedImmersion_factorization_of_locallyOfFiniteType
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y] :
    (MorphismProperty.comp
      (@IsClosedImmersion S : MorphismProperty (AlgebraicSpace S))
      (@FinitePresentation S : MorphismProperty (AlgebraicSpace S))) f :=
  sorry

/-- A finite type separated morphism of algebraic spaces over a scheme, with
quasi-compact quasi-separated target, factors as a closed immersion followed by
a separated morphism of finite presentation. -/
theorem exists_closedImmersion_factorization_of_finiteType_separated
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [Separated f]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y] :
    (MorphismProperty.comp
      (@IsClosedImmersion S : MorphismProperty (AlgebraicSpace S))
      ((@FinitePresentation S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Separated S : MorphismProperty (AlgebraicSpace S)))) f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
