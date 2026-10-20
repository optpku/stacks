module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Pullback
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Finite type and locally finite type morphisms of formal spaces

The property is tested on the actual algebraic-space pullback along each scheme section.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A morphism of functors of points on schemes over `S` is locally of finite type
when it is representable by algebraic spaces and every Yoneda pullback is locally
of finite type as a morphism of algebraic spaces. -/
@[mk_iff]
class LocallyOfFiniteType {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Prop where
  /-- `f` is representable by algebraic spaces. -/
  representable : AlgebraicSpace.representableByAlgebraicSpaces f
  /-- Every Yoneda pullback of `f` is locally of finite type. -/
  of_pullback :
    ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.LocallyOfFiniteType
        (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom representable ξ)

namespace LocallyOfFiniteType

/-- The identity morphism of a functor of points is locally of finite type. -/
instance id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} : LocallyOfFiniteType (𝟙 X) :=
  sorry

/-- A locally of finite type morphism is representable by algebraic spaces,
and every Yoneda pullback is locally of finite type. -/
theorem spec {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [hf : LocallyOfFiniteType f] :
    AlgebraicSpace.representableByAlgebraicSpaces f ∧
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
        AlgebraicSpace.LocallyOfFiniteType
          (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom hf.representable ξ) :=
  sorry

/-- The composite of two locally of finite type morphisms of functors of points
is locally of finite type. -/
instance comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType f] [LocallyOfFiniteType g] :
    LocallyOfFiniteType (f ≫ g) :=
  sorry

end LocallyOfFiniteType

/-- A morphism of functors of points on schemes over `S` is of finite type when
it is representable by algebraic spaces and every Yoneda pullback is of finite
type as a morphism of algebraic spaces. -/
@[mk_iff]
class FiniteType {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Prop where
  /-- `f` is representable by algebraic spaces. -/
  representable : AlgebraicSpace.representableByAlgebraicSpaces f
  /-- Every Yoneda pullback of `f` is of finite type. -/
  of_pullback :
    ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.FiniteType
        (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom representable ξ)

namespace FiniteType

/-- The identity morphism of a functor of points is of finite type. -/
instance id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} : FiniteType (𝟙 X) :=
  sorry

/-- A finite-type morphism is representable by algebraic spaces, and every
Yoneda pullback is of finite type. -/
theorem spec {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [hf : FiniteType f] :
    AlgebraicSpace.representableByAlgebraicSpaces f ∧
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
        AlgebraicSpace.FiniteType
          (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom hf.representable ξ) :=
  sorry

/-- A finite type morphism of functors of points is locally of finite type. -/
instance instLocallyOfFiniteType {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) [FiniteType f] : LocallyOfFiniteType f :=
  sorry

end FiniteType

/-- Finite type morphisms of functors of points are stable under composition. -/
instance finiteType_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@FiniteType S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u)) :=
  sorry

/-- The composite of two finite type morphisms of functors of points is of finite type. -/
instance finiteType_comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Y ⟶ Z) [FiniteType f] [FiniteType g] :
    FiniteType (f ≫ g) :=
  MorphismProperty.comp_mem (@FiniteType S) f g inferInstance inferInstance

/-- Locally of finite type morphisms of functors of points are stable under composition. -/
instance locallyOfFiniteType_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@LocallyOfFiniteType S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u)) where
  comp_mem {X Y Z} f g hf hg := @LocallyOfFiniteType.comp S X Y Z f g hf hg

end AlgebraicGeometry.FormalAlgebraicSpace
