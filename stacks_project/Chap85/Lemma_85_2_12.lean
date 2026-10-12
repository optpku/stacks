/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import stacks_project.Chap85.Lemma_85_2_1_Site
public import stacks_project.Chap85.Lemma_85_2_5_Component
public import stacks_project.Chap85.Lemma_85_2_12_Projection

/-!
# The morphism of topoi from a constant simplicial space

For a topological space `X` viewed as a constant simplicial space, the degree-forgetting
functor `U ↦ U` from `X_{•,Zar}` to `X_Zar` is continuous and cocontinuous, and induces a
morphism of topoi `g : Sh(X_{•,Zar}) ⟶ Sh(X)` together with a left adjoint `g_!` of `g⁻¹`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped Simplicial CategoryTheory.MorphismOfTopoiIn

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject

variable (X : TopCat.{u})

section MorphismOfTopoi

variable [HasSheafify (zariskiTopology (constSpace X)) (Type u)]
variable [∀ F : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u,
    (constProjection X).op.HasPointwiseRightKanExtension F]

/-- The degree-forgetting functor `X_{•,Zar} ⟶ X_Zar`, `U ↦ U`, is continuous and
cocontinuous and defines a morphism of topoi `g : Sh(X_{•,Zar}) ⟶ Sh(X)`. -/
@[stacks 09W3]
def constMorphism :
    MorphismOfTopoiIn (Opens.grothendieckTopology X) (zariskiTopology (constSpace X)) :=
  (constProjection X).morphismOfTopoiInOfCocontinuous
    (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X)

/-- The canonical comparison from the topos inverse image of `constMorphism` to continuous
precomposition along `constProjection`. -/
def constMorphism_inverseImage_iso
    [HasWeakSheafify (zariskiTopology (constSpace X)) (Type u)]
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] :
    (constMorphism X)⁻¹ ≅
      (constProjection X).sheafPushforwardContinuous (Type u)
        (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X) :=
  _root_.CategoryTheory.eqToIso
      (morphismOfTopoiInOfCocontinuous_inverseImage (constProjection X)
        (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X)) ≪≫
    asIso
      (CocontinuousPullback.comparison (constProjection X)
        (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X))

/-- Degree-`n` restriction of the continuous inverse image along `constProjection` is the
identity on sheaves on `X`. -/
def inverseImage_const_app (n : SimplexCategory)
    (F : Sheaf (Opens.grothendieckTopology X) (Type u)) :
    ((toCosimplicial X (Type u)).obj
        (((constProjection X).sheafPushforwardContinuous (Type u)
          (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X)).obj F)).obj n ≅ F :=
  (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) (Type u)).preimageIso
    (isoWhiskerRight ((NatIso.op (fiber_comp_constProjection X (op n))).symm) F.obj ≪≫
      F.obj.leftUnitor)

/-- Lemma 85.2.12 (1): `g⁻¹` associates to a sheaf on `X` the constant cosimplicial
sheaf on `X`. -/
@[stacks 09W3]
def inverseImage_const (F : Sheaf (Opens.grothendieckTopology X) (Type u)) :
    (toCosimplicial X (Type u)).obj
        (((constProjection X).sheafPushforwardContinuous (Type u)
          (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X)).obj F) ≅
      (CosimplicialObject.const (Sheaf (Opens.grothendieckTopology X) (Type u))).obj F where
  hom :=
    { app := fun n ↦ (inverseImage_const_app X n F).hom
      naturality := sorry }
  inv :=
    { app := fun n ↦ (inverseImage_const_app X n F).inv
      naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

section LowerShriek

variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
variable [∀ F : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u,
    (constProjection X).op.HasLeftKanExtension F]

/-- The left adjoint `g_!` of `g⁻¹`, given by sheafified left Kan extension along
`constProjection`. -/
def constLowerShriek :
    Sheaf (zariskiTopology (constSpace X)) (Type u) ⥤
      Sheaf (Opens.grothendieckTopology X) (Type u) :=
  (constProjection X).sheafPullback (Type u) (zariskiTopology (constSpace X))
    (Opens.grothendieckTopology X)

/-- `g_!` is left adjoint to continuous inverse image along `constProjection`. -/
def constLowerShriekAdjunction :
    constLowerShriek X ⊣
      (constProjection X).sheafPushforwardContinuous (Type u)
        (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X) :=
  (constProjection X).sheafAdjunctionContinuous (Type u) (zariskiTopology (constSpace X))
    (Opens.grothendieckTopology X)

/-- The canonical comparison `F ⟶ g⁻¹ F_0` induced by the unique maps to `⦋0⦌`. -/
def toInverseImageComponentZero
    (F : Sheaf (zariskiTopology (constSpace X)) (Type u)) :
    F ⟶
      ((constProjection X).sheafPushforwardContinuous (Type u)
        (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X)).obj
        ((sheafComponent (constSpace X) 0 (Type u)).obj F) :=
  ObjectProperty.homMk
    { app := fun U ↦
        let V := U.unop
        F.obj.map
          (Quiver.Hom.op
            (@DiagramOpens.homMk _ _ (constSpace X)
              (DiagramOpens.ofOpens (constSpace X) (op ⦋0⦌) V.opens) V
              (SimplexCategory.const V.base.unop ⦋0⦌ 0).op fun x hx ↦ hx))
      naturality := sorry }

/-- Lemma 85.2.12 (2): `g_!` associates to a sheaf `F` on `X_{•,Zar}` the sheaf `F_0`. -/
@[stacks 09W3]
def lowerShriekIsoComponentZero
    (F : Sheaf (zariskiTopology (constSpace X)) (Type u)) :
    (constLowerShriek X).obj F ≅ (sheafComponent (constSpace X) 0 (Type u)).obj F where
  hom :=
    ((constLowerShriekAdjunction X).homEquiv F
        ((sheafComponent (constSpace X) 0 (Type u)).obj F)).symm
      (toInverseImageComponentZero X F)
  inv :=
    (sheafComponent (constSpace X) 0 (Type u)).map
        ((constLowerShriekAdjunction X).unit.app F) ≫
      (inverseImage_const_app X ⦋0⦌ ((constLowerShriek X).obj F)).hom
  hom_inv_id := sorry
  inv_hom_id := sorry

end LowerShriek

/-- The canonical comparison from `g_* F` to the degree-zero component `F_0`. -/
def pushforwardι (F : Sheaf (zariskiTopology (constSpace X)) (Type u)) :
    (constMorphism X).pushforward.obj F ⟶ ((toCosimplicial X (Type u)).obj F) ^⦋0⦌ :=
  (inverseImage_const X ((constMorphism X).pushforward.obj F)).inv.app ⦋0⦌ ≫
    ((toCosimplicial X (Type u)).map
      (((constProjection X).sheafAdjunctionCocontinuous (Type u)
          (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X)).counit.app F)).app ⦋0⦌

/-- The two coface maps `F_0 ⇉ F_1` coequalize `pushforwardι F`. -/
theorem pushforwardFork_condition (F : Sheaf (zariskiTopology (constSpace X)) (Type u)) :
    pushforwardι X F ≫ ((toCosimplicial X (Type u)).obj F).δ (0 : Fin 2) =
      pushforwardι X F ≫ ((toCosimplicial X (Type u)).obj F).δ (1 : Fin 2) :=
  sorry

/-- The fork presenting `g_* F` as a candidate equalizer of `F_0 ⇉ F_1`. -/
def pushforwardFork (F : Sheaf (zariskiTopology (constSpace X)) (Type u)) :
    Fork (((toCosimplicial X (Type u)).obj F).δ (0 : Fin 2))
      (((toCosimplicial X (Type u)).obj F).δ (1 : Fin 2)) :=
  Fork.ofι (pushforwardι X F) (pushforwardFork_condition X F)

/-- The mediating morphism from a test cone into `g_* F`, obtained by adjunction from
the degree-zero comparison of the test cone. -/
def pushforwardForkLift (F : Sheaf (zariskiTopology (constSpace X)) (Type u))
    (s : Fork (((toCosimplicial X (Type u)).obj F).δ (0 : Fin 2))
      (((toCosimplicial X (Type u)).obj F).δ (1 : Fin 2))) :
    s.pt ⟶ (constMorphism X).pushforward.obj F :=
  ((constProjection X).sheafAdjunctionCocontinuous (Type u)
      (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X)).homEquiv
    s.pt F
    (ObjectProperty.homMk
      { app := fun U ↦
          let V := U.unop
          (Fork.ι s).hom.app (op V.opens) ≫
            F.obj.map
              (Quiver.Hom.op
                (@DiagramOpens.homMk _ _ (constSpace X) V
                  (DiagramOpens.ofOpens (constSpace X) (op ⦋0⦌) V.opens)
                  (SimplexCategory.const ⦋0⦌ V.base.unop 0).op fun x hx ↦ hx))
        naturality := sorry })

/-- Lemma 85.2.12 (3): `g_*` associates to a sheaf `F` on `X_{•,Zar}` the equalizer of
the two maps `F_0 ⟶ F_1`. -/
@[stacks 09W3]
def pushforwardFork_isLimit (F : Sheaf (zariskiTopology (constSpace X)) (Type u)) :
    IsLimit (pushforwardFork X F) :=
  Fork.IsLimit.mk (pushforwardFork X F) (pushforwardForkLift X F) sorry sorry

end MorphismOfTopoi

end CategoryTheory.SimplicialObject
