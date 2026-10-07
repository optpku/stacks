module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Property

/-!
# Proper morphisms of formal algebraic spaces

A morphism of functors of points on schemes over `S` is proper when it is
representable by algebraic spaces and every Yoneda pullback is a proper
morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A morphism of functors of points on schemes over `S` is proper when it is
representable by algebraic spaces and every Yoneda pullback is a proper
morphism of algebraic spaces. -/
@[mk_iff]
class Proper {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Prop where
  /-- `f` is representable by algebraic spaces. -/
  representable : AlgebraicSpace.representableByAlgebraicSpaces f
  /-- Every Yoneda pullback of `f` is a proper morphism of algebraic spaces. -/
  of_pullback :
    ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.Proper
        (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom representable ξ)

namespace Proper

/-- The identity morphism of a functor of points is proper. -/
instance id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} : Proper (𝟙 X) :=
  sorry

/-- An isomorphism of functors of points is proper. -/
instance of_isIso {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [IsIso f] : Proper f :=
  sorry

/-- A proper morphism of functors of points is representable by algebraic spaces,
and every Yoneda pullback is a proper morphism of algebraic spaces. -/
theorem spec {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [hf : Proper f] :
    AlgebraicSpace.representableByAlgebraicSpaces f ∧
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
        AlgebraicSpace.Proper
          (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom hf.representable ξ) :=
  sorry

/-- A morphism of functors of points is proper if and only if it satisfies the
Bootstrap transfer of `AlgebraicSpace.Proper`. -/
theorem iff_relativeAlgebraicSpaces {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    Proper f ↔ AlgebraicSpace.relativeAlgebraicSpaces (@AlgebraicSpace.Proper S) f :=
  sorry

end Proper

end AlgebraicGeometry.FormalAlgebraicSpace
