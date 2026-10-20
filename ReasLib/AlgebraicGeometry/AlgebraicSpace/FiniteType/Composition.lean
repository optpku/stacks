module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of finite type morphisms of algebraic spaces

The composition of a pair of finite type morphisms of algebraic spaces is of
finite type, and the same holds for morphisms locally of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Locally quasi-finite morphisms are locally of finite type. -/
instance locallyOfFiniteType_of_locallyQuasiFinite {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyQuasiFinite f] :
    LocallyOfFiniteType f := sorry

/-- Open immersions are locally of finite type. -/
instance locallyOfFiniteType_of_isOpenImmersion {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsOpenImmersion f] :
    LocallyOfFiniteType f := sorry

/-- Closed immersions are locally of finite type. -/
instance locallyOfFiniteType_of_isClosedImmersion {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsClosedImmersion f] :
    LocallyOfFiniteType f := sorry

/-- Finite type morphisms of algebraic spaces are stable under composition. -/
@[stacks 03XG]
instance finiteType_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@FiniteType S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of finite type morphisms of algebraic spaces is of finite
type. -/
instance finiteType_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [FiniteType f] [FiniteType g] :
    FiniteType (f ≫ g) :=
  MorphismProperty.comp_mem (@FiniteType S) f g inferInstance inferInstance

/-- Morphisms of algebraic spaces locally of finite type are stable under composition. -/
@[stacks 03XG]
instance locallyOfFiniteType_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@LocallyOfFiniteType S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of locally of finite type morphisms of algebraic spaces is
locally of finite type. -/
instance locallyOfFiniteType_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType f] [LocallyOfFiniteType g] :
    LocallyOfFiniteType (f ≫ g) :=
  MorphismProperty.comp_mem (@LocallyOfFiniteType S) f g inferInstance inferInstance

/-- The structure morphism of an open subspace remains locally of finite type. -/
def locallyOfFiniteType_openSubspace_comp {S : Scheme.{u}}
    {X B : AlgebraicSpace S} (U : OpenSubspace X) (f : X ⟶ B)
    [LocallyOfFiniteType f] : LocallyOfFiniteType (U.ι ≫ f) :=
  MorphismProperty.comp_mem (@LocallyOfFiniteType S) U.ι f
    (@locallyOfFiniteType_of_isOpenImmersion _ _ _ U.ι U.isOpenImmersion) inferInstance

/-- The structure morphism of a closed subspace remains locally of finite type. -/
def locallyOfFiniteType_closedSubspace_comp {S : Scheme.{u}}
    {X B : AlgebraicSpace S} (W : ClosedSubspace X) (f : X ⟶ B)
    [LocallyOfFiniteType f] : LocallyOfFiniteType (W.ι ≫ f) :=
  MorphismProperty.comp_mem (@LocallyOfFiniteType S) W.ι f
    (@locallyOfFiniteType_of_isClosedImmersion _ _ _ W.ι W.isClosedImmersion) inferInstance

end AlgebraicGeometry.AlgebraicSpace
