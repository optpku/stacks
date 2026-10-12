/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap88.Definition_88_21_1_Formal

/-!
# Finite type morphisms of formal algebraic spaces

A morphism of functors of points on schemes over `S` is of finite type when it
is representable by algebraic spaces and every Yoneda pullback is of finite
type as a morphism of algebraic spaces. This is the Bootstrap transfer of
`AlgebraicSpace.FiniteType`, equivalently locally of finite type and
quasi-compact on those pullbacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

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

end AlgebraicGeometry.FormalAlgebraicSpace
