/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Descent from pre-relation quotient sheaves

This module provides the categorical descent morphism associated to an equalizing map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- An equalizing sheaf map identifies points related by a pre-relation. -/
theorem quotientSheafLift_respects {S : Scheme.{u}} {U : Over S}
    (J : GrothendieckTopology (Over S)) [J.Subcanonical] (P : PreRelation U)
    {F : Sheaf J (Type (u + 1))} (q : J.uliftYoneda.{u + 1}.obj U ⟶ F)
    (h : J.uliftYoneda.{u + 1}.map P.t ≫ q = J.uliftYoneda.{u + 1}.map P.s ≫ q)
    {T : Over S} {x y : T ⟶ U} (hxy : P.pointRel T x y) :
    q.hom.app (op T) ⟨x⟩ = q.hom.app (op T) ⟨y⟩ :=
  sorry

/-- The pointwise descent map on universe-raised quotient classes. -/
def quotientSheafLiftApp {S : Scheme.{u}} {U : Over S}
    (J : GrothendieckTopology (Over S)) [J.Subcanonical] (P : PreRelation U)
    {F : Sheaf J (Type (u + 1))} (q : J.uliftYoneda.{u + 1}.obj U ⟶ F)
    (h : J.uliftYoneda.{u + 1}.map P.t ≫ q = J.uliftYoneda.{u + 1}.map P.s ≫ q)
    (T : (Over S)ᵒᵖ) :
    (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u}).obj T ⟶ F.obj.obj T :=
  TypeCat.ofHom fun (x : ULift (Quot (P.pointRel T.unop))) ↦
    Quot.lift (fun a : T.unop ⟶ U ↦ q.hom.app T ⟨a⟩)
      (fun _ _ hab ↦ quotientSheafLift_respects J P q h hab) x.down

/-- The pointwise descent maps are natural in the test scheme. -/
theorem quotientSheafLiftApp_naturality {S : Scheme.{u}} {U : Over S}
    (J : GrothendieckTopology (Over S)) [J.Subcanonical] (P : PreRelation U)
    {F : Sheaf J (Type (u + 1))} (q : J.uliftYoneda.{u + 1}.obj U ⟶ F)
    (h : J.uliftYoneda.{u + 1}.map P.t ≫ q = J.uliftYoneda.{u + 1}.map P.s ≫ q)
    ⦃T T' : (Over S)ᵒᵖ⦄ (f : T ⟶ T') :
    (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u}).map f ≫
        quotientSheafLiftApp J P q h T' =
      quotientSheafLiftApp J P q h T ≫ F.obj.map f :=
  sorry

/-- The presheaf-level descent of an equalizing sheaf map. -/
def quotientPresheafLift {S : Scheme.{u}} {U : Over S}
    (J : GrothendieckTopology (Over S)) [J.Subcanonical] (P : PreRelation U)
    {F : Sheaf J (Type (u + 1))} (q : J.uliftYoneda.{u + 1}.obj U ⟶ F)
    (h : J.uliftYoneda.{u + 1}.map P.t ≫ q = J.uliftYoneda.{u + 1}.map P.s ≫ q) :
    P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u} ⟶ F.obj where
  app T := quotientSheafLiftApp J P q h T
  naturality := quotientSheafLiftApp_naturality J P q h

/-- The sheaf morphism induced by an equalizing map from the representing sheaf. -/
def quotientSheafLift {S : Scheme.{u}} {U : Over S}
    (J : GrothendieckTopology (Over S)) [J.Subcanonical] (P : PreRelation U)
    {F : Sheaf J (Type (u + 1))} (q : J.uliftYoneda.{u + 1}.obj U ⟶ F)
    (h : J.uliftYoneda.{u + 1}.map P.t ≫ q = J.uliftYoneda.{u + 1}.map P.s ≫ q) :
    P.quotientSheaf J ⟶ F :=
  ((sheafificationAdjunction J (Type (u + 1))).homEquiv
      (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u}) F).symm
    (quotientPresheafLift J P q h)

/-- The quotient map followed by descent recovers the original equalizing map. -/
theorem quotientMap_comp_quotientSheafLift {S : Scheme.{u}} {U : Over S}
    (J : GrothendieckTopology (Over S)) [J.Subcanonical] (P : PreRelation U)
    {F : Sheaf J (Type (u + 1))} (q : J.uliftYoneda.{u + 1}.obj U ⟶ F)
    (h : J.uliftYoneda.{u + 1}.map P.t ≫ q = J.uliftYoneda.{u + 1}.map P.s ≫ q) :
    P.quotientMap J ≫ quotientSheafLift J P q h = q :=
  sorry

/-- The quotient sheaf maps canonically to the categorical coequalizer of the represented relation.
-/
def quotientSheafToCoequalizer {S : Scheme.{u}} {U : Over S}
    (J : GrothendieckTopology (Over S)) [J.Subcanonical] (P : PreRelation U) :
    P.quotientSheaf J ⟶
      coequalizer (J.uliftYoneda.{u + 1}.map P.t) (J.uliftYoneda.{u + 1}.map P.s) :=
  quotientSheafLift J P
    (coequalizer.π (J.uliftYoneda.{u + 1}.map P.t) (J.uliftYoneda.{u + 1}.map P.s))
    (coequalizer.condition _ _)

/-- The quotient-sheaf comparison is an isomorphism. -/
instance isIso_quotientSheafToCoequalizer {S : Scheme.{u}} {U : Over S}
    (J : GrothendieckTopology (Over S)) [J.Subcanonical] (P : PreRelation U) :
    IsIso (quotientSheafToCoequalizer J P) := sorry

end AlgebraicGeometry.Scheme.PreRelation
