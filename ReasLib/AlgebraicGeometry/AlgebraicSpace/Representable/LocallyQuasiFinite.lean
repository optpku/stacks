/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.Cancellation

/-!
# Locally quasi-finite morphisms representable by algebraic spaces

A morphism from a scheme to a presheaf that is representable by algebraic
spaces and locally quasi-finite is representable by schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism from a scheme over `S` to a presheaf on schemes over `S` is
representable by schemes if it is representable by algebraic spaces and its
pullbacks along all Yoneda sections are locally of finite type and locally
quasi-finite. Local finite type together with chartwise local quasi-finiteness
expresses local quasi-finiteness in the Stacks convention. -/
theorem relativelyRepresentable_of_locallyQuasiFinite
    {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u} {X : Over S}
    (a : yoneda.obj X ⟶ F) (ha : representableByAlgebraicSpaces a)
    (h_locallyOfFiniteType :
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ F), LocallyOfFiniteType (ha.pullbackHom ξ))
    (h_locallyQuasiFinite :
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ F), LocallyQuasiFinite (ha.pullbackHom ξ)) :
    yoneda.relativelyRepresentable a :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
