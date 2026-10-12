/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import stacks_project.Chap92.Lemma_92_7_1_Omega

/-!
# The abelian presheaf `Ω_{O/A}` on the polynomial site

This leaf owns `Ω_{O/A}` as a functor `(PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat`, sending a
polynomial arrow `P ⟶ B` to the additive group of Kähler differentials `Ω[P ⁄ A]`. This is
not the same object as `omegaSheaf`, whose sections are the tensored modules
`Ω[P ⁄ A] ⊗[P] B`.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

namespace CommAlgCat.Over.Polynomial.Site

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The additive group of Kähler differentials of a polynomial arrow `P ⟶ B`. -/
def kaehlerObj (X : Algebra.PolynomialOver A B) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (Ω[X.obj.left ⁄ A])

/-- Unfolding `kaehlerObj` recovers the unbundled Kähler group `Ω[P ⁄ A]`. -/
theorem kaehlerObj_eq (X : Algebra.PolynomialOver A B) :
    kaehlerObj X = AddCommGrpCat.of (Ω[X.obj.left ⁄ A]) :=
  sorry

/-- The map on Kähler groups induced by a morphism of polynomial arrows, in the presence of
the induced `P`-algebra structure on `P'`. -/
def kaehlerMapWith {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y)
    [Algebra X.obj.left Y.obj.left]
    [IsScalarTower A X.obj.left Y.obj.left] :
    kaehlerObj X ⟶ kaehlerObj Y :=
  AddCommGrpCat.ofHom
    (KaehlerDifferential.map A A X.obj.left Y.obj.left).toAddMonoidHom

/-- The map on Kähler groups induced by a morphism of polynomial arrows over `B`. -/
def kaehlerMap {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y) :
    kaehlerObj X ⟶ kaehlerObj Y :=
  @kaehlerMapWith A B _ _ _ X Y f (algebraOfHom f)
    (@isScalarTower_algebraOfHom A B _ _ _ X Y f (algebraOfHom f))

/-- Unfolding `kaehlerMap` recovers `KaehlerDifferential.map` of the underlying ring map. -/
theorem kaehlerMap_eq {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y) :
    kaehlerMap f =
      @kaehlerMapWith A B _ _ _ X Y f (algebraOfHom f)
        (@isScalarTower_algebraOfHom A B _ _ _ X Y f (algebraOfHom f)) :=
  sorry

/-- Identity morphisms act as the identity on Kähler groups. -/
theorem kaehlerMap_id (X : Algebra.PolynomialOver A B) :
    kaehlerMap (𝟙 X) = 𝟙 (kaehlerObj X) :=
  sorry

/-- Composition of polynomial-arrow morphisms maps to composition of Kähler maps. -/
theorem kaehlerMap_comp {X Y Z : Algebra.PolynomialOver A B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    kaehlerMap (f ≫ g) = kaehlerMap f ≫ kaehlerMap g :=
  sorry

variable (A B) in
/-- The covariant functor of Kähler groups on polynomial arrows `P ⟶ B`. -/
def kaehlerCov : Algebra.PolynomialOver A B ⥤ AddCommGrpCat.{u} where
  obj := kaehlerObj
  map f := kaehlerMap f
  map_id X := kaehlerMap_id X
  map_comp f g := kaehlerMap_comp f g

/-- Objects of `kaehlerCov` are the Kähler groups of the corresponding polynomial arrow. -/
theorem kaehlerCov_obj (X : Algebra.PolynomialOver A B) :
    (kaehlerCov A B).obj X = kaehlerObj X :=
  sorry

variable (A B) in
/-- The abelian presheaf `Ω_{O/A}` on `C_{B/A}`, sending `(P, α)` to `Ω[P ⁄ A]`. -/
def kaehlerPresheaf : (Algebra.PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  unopUnop (Algebra.PolynomialOver A B) ⋙ kaehlerCov A B

/-- Evaluating `kaehlerPresheaf` on a double-opposite polynomial arrow recovers `kaehlerObj`. -/
theorem kaehlerPresheaf_obj (X : (Algebra.PolynomialSite A B)ᵒᵖ) :
    (kaehlerPresheaf A B).obj X = kaehlerObj (unop (unop X)) :=
  sorry

/-- `kaehlerPresheaf` is precomposition of `kaehlerCov` with the double-opposite equivalence. -/
theorem kaehlerPresheaf_eq :
    kaehlerPresheaf A B = unopUnop (Algebra.PolynomialOver A B) ⋙ kaehlerCov A B :=
  sorry

/-- Components of `kaehlerPresheaf` on morphisms are `kaehlerMap` of the underlying polynomial
arrow. -/
theorem kaehlerPresheaf_map {X Y : (Algebra.PolynomialSite A B)ᵒᵖ} (f : X ⟶ Y) :
    (kaehlerPresheaf A B).map f = kaehlerMap f.unop.unop :=
  sorry

end CommAlgCat.Over.Polynomial.Site

