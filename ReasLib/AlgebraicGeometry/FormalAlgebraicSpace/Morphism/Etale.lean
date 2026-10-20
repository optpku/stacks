/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Pullback

/-!
# Étale morphisms of functors of points

A morphism of functors of points on schemes over `S` is étale when it is
representable by algebraic spaces and every Yoneda pullback is an étale
morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A morphism of functors of points on schemes over `S` is étale when it is
representable by algebraic spaces and every Yoneda pullback is étale. -/
@[mk_iff]
class Etale {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Prop where
  /-- `f` is representable by algebraic spaces. -/
  representable : representableByAlgebraicSpaces f
  /-- Every Yoneda pullback of `f` is an étale morphism of algebraic spaces. -/
  of_pullback :
    ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.Etale (representableByAlgebraicSpaces.pullbackHom representable ξ)

namespace Etale

/-- The identity morphism of a functor of points is étale. -/
instance id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} : Etale (𝟙 X) := sorry

/-- An étale morphism is representable by algebraic spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) [Etale f] : representableByAlgebraicSpaces f :=
  sorry

/-- Yoneda pullbacks of an étale morphism are étale morphisms of algebraic
spaces. -/
theorem spec {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [hf : Etale f] {U : Over S} (ξ : yoneda.obj U ⟶ Y) :
    representableByAlgebraicSpaces f ∧
      AlgebraicSpace.Etale
        (representableByAlgebraicSpaces.pullbackHom hf.representable ξ) :=
  sorry

end Etale

end AlgebraicGeometry.FormalAlgebraicSpace
