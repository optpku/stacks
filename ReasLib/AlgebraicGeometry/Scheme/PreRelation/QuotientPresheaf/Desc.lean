/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientPresheaf

/-!
# Descent from quotient presheaves

An equalizing map into any presheaf descends along the objectwise quotient.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- Related points of a pre-relation become equal after composing with an equalizing
morphism into a presheaf. -/
theorem quotientPresheafDescTo_respects {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) {F : (Over S)ᵒᵖ ⥤ Type u} (q : yoneda.obj U ⟶ F)
    (h_equalizes : yoneda.map P.t ≫ q = yoneda.map P.s ≫ q) {T : (Over S)ᵒᵖ}
    {x y : T.unop ⟶ U} (hxy : P.pointRel T.unop x y) :
    q.app T x = q.app T y :=
  sorry

/-- Quotient elimination for an equalizing map commutes with restriction. -/
theorem quotientPresheafDescTo_naturality {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) {F : (Over S)ᵒᵖ ⥤ Type u} (q : yoneda.obj U ⟶ F)
    (h_equalizes : yoneda.map P.t ≫ q = yoneda.map P.s ≫ q)
    {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') :
    P.quotientPresheaf.map f ≫
      (TypeCat.ofHom <| Quot.lift (fun x : T'.unop ⟶ U ↦ q.app T' x)
        (fun _ _ hxy ↦ quotientPresheafDescTo_respects P q h_equalizes hxy)) =
    (TypeCat.ofHom <| Quot.lift (fun x : T.unop ⟶ U ↦ q.app T x)
      (fun _ _ hxy ↦ quotientPresheafDescTo_respects P q h_equalizes hxy)) ≫ F.map f :=
  sorry

/-- Descent of a morphism out of `U` along the objectwise quotient of `P`. -/
def quotientPresheafDescTo {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
    {F : (Over S)ᵒᵖ ⥤ Type u} (q : yoneda.obj U ⟶ F)
    (h_equalizes : yoneda.map P.t ≫ q = yoneda.map P.s ≫ q) :
    P.quotientPresheaf ⟶ F where
  app T :=
    TypeCat.ofHom <|
      Quot.lift (fun x : T.unop ⟶ U ↦ q.app T x) fun _ _ hxy ↦
        quotientPresheafDescTo_respects P q h_equalizes hxy
  naturality {T T'} f := quotientPresheafDescTo_naturality P q h_equalizes f

/-- The descended map evaluates on a quotient representative as the original map. -/
theorem quotientPresheafDescTo_mk {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) {F : (Over S)ᵒᵖ ⥤ Type u} (q : yoneda.obj U ⟶ F)
    (h_equalizes : yoneda.map P.t ≫ q = yoneda.map P.s ≫ q)
    (T : Over S) (x : T ⟶ U) :
    (quotientPresheafDescTo P q h_equalizes).app (op T) (Quot.mk (P.pointRel T) x) =
      q.app (op T) x :=
  rfl

end AlgebraicGeometry.Scheme.PreRelation
