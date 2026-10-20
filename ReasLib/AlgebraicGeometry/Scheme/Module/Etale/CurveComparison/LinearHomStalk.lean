/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.LinearSheafHom
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Point.FiniteLinearLift
public import ReasLib.CategoryTheory.Sites.Point.OverFiber
public import ReasLib.CategoryTheory.Sites.LocallyConstant.PointedChart
public import Mathlib.CategoryTheory.Sites.CoverLifting

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
noncomputable section
universe u

namespace ActualLinearHomStalk
variable {Y : Scheme.{u}}
variable (R : Type (u + 1)) [CommRing R] (xbar : GeometricPoint Y)
variable (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))

/-- A common pointed neighborhood representing the local morphism germ and
the input germ. The equalities fix exactly which elements are represented. -/
structure Representative
    (α : (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj
        (ActualLinearSheafHom.obj Y R F G))
    (s : (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj F) where
  U : Y.Etale
  point : xbar.toSmallEtalePoint.fiber.obj U
  morphism : (ActualLinearSheafHom.obj Y R F G).obj.obj (op U)
  sectionValue : F.obj.obj (op U)
  morphism_germ : xbar.toSmallEtalePoint.toPresheafFiber U point
    (ActualLinearSheafHom.obj Y R F G).obj morphism = α
  section_germ : xbar.toSmallEtalePoint.toPresheafFiber U point F.obj sectionValue = s

/-- Choose representatives using the native stalk colimit, then restrict both values to
an actual common pointed neighborhood. -/
def representative
    (α : (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj
        (ActualLinearSheafHom.obj Y R F G))
    (s : (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj F) :
    Representative R xbar F G α s := by
  classical
  letI : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1}
      (CategoryTheory.forget (ModuleCat.{u + 1} R))
  let Φ := xbar.toSmallEtalePoint
  let H := ActualLinearSheafHom.obj Y R F G
  let hα := Φ.toPresheafFiber_jointly_surjective (P := H.obj) α
  let hs := Φ.toPresheafFiber_jointly_surjective (P := F.obj) s
  let Uα : Y.Etale := hα.choose
  let pα : Φ.fiber.obj Uα := hα.choose_spec.choose
  let zα : H.obj.obj (op Uα) := hα.choose_spec.choose_spec.choose
  let Us : Y.Etale := hs.choose
  let ps : Φ.fiber.obj Us := hs.choose_spec.choose
  let zs : F.obj.obj (op Us) := hs.choose_spec.choose_spec.choose
  let A : Φ.fiber.Elements := ⟨Uα, pα⟩
  let B : Φ.fiber.Elements := ⟨Us, ps⟩
  let N := IsCofiltered.min A B
  let left := IsCofiltered.minToLeft A B
  let right := IsCofiltered.minToRight A B
  exact
    { U := N.1
      point := N.2
      morphism := H.obj.map left.val.op zα
      sectionValue := F.obj.map right.val.op zs
      morphism_germ := by
        have h := ConcreteCategory.congr_hom (Φ.toPresheafFiber_w left.val N.2 H.obj) zα
        rw [left.property] at h
        exact h.trans hα.choose_spec.choose_spec.choose_spec
      section_germ := by
        have h := ConcreteCategory.congr_hom (Φ.toPresheafFiber_w right.val N.2 F.obj) zs
        rw [right.property] at h
        exact h.trans hs.choose_spec.choose_spec.choose_spec }

/-- Filteredness gives a common representative for two germs. -/
theorem representative_nonempty
    (α : (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj
        (ActualLinearSheafHom.obj Y R F G))
    (s : (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj F) :
    Nonempty (Representative R xbar F G α s) :=
  ⟨representative R xbar F G α s⟩

/-- Evaluate the local linear morphism before taking its germ. -/
def evaluateRepresentative
    {α : (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj
        (ActualLinearSheafHom.obj Y R F G)}
    {s : (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj F}
    (r : Representative R xbar F G α s) :
    (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj G :=
  xbar.toSmallEtalePoint.toPresheafFiber r.U r.point G.obj
    ((r.morphism.app (op (Over.mk (𝟙 r.U)))).hom r.sectionValue)

/-- Germ evaluation does not depend on the common representative. -/
theorem evaluateRepresentative_eq
    {α : (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj
        (ActualLinearSheafHom.obj Y R F G)}
    {s : (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj F}
    (r t : Representative R xbar F G α s) :
    evaluateRepresentative R xbar F G r = evaluateRepresentative R xbar F G t := sorry

/-- Evaluate the local morphism and input on a common pointed neighborhood,
then take the germ of the resulting section. -/
def evaluate
    (α : (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj
        (ActualLinearSheafHom.obj Y R F G))
    (s : (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj F) :
    (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj G :=
  evaluateRepresentative R xbar F G (representative R xbar F G α s)

/-- On germs from the same pointed neighborhood, evaluation is the germ of local evaluation. -/
theorem evaluate_germ (U : Y.Etale) (p : xbar.toSmallEtalePoint.fiber.obj U)
    (α : (ActualLinearSheafHom.obj Y R F G).obj.obj (op U)) (s : F.obj.obj (op U)) :
    evaluate R xbar F G
        (xbar.toSmallEtalePoint.toPresheafFiber U p
          (ActualLinearSheafHom.obj Y R F G).obj α)
        (xbar.toSmallEtalePoint.toPresheafFiber U p F.obj s) =
      xbar.toSmallEtalePoint.toPresheafFiber U p G.obj
        ((α.app (op (Over.mk (𝟙 U)))).hom s) :=
  evaluateRepresentative_eq R xbar F G _
    { U := U
      point := p
      morphism := α
      sectionValue := s
      morphism_germ := rfl
      section_germ := rfl }

/-- The explicit local evaluation is linear in both the morphism and its input. -/
def map : (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj
    (ActualLinearSheafHom.obj Y R F G) →ₗ[R]
    ((xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj F →ₗ[R]
        (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj G) where
  toFun α :=
    { toFun := evaluate R xbar F G α
      map_add' := sorry
      map_smul' := sorry }
  map_add' := sorry
  map_smul' := sorry

variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)]

/-- Restricting a constant module sheaf along a map of neighborhoods keeps its constant model.
Both directions come from the native sheafification/continuous-pushforward comparison. -/
def constantRestrictionIso {U W : Y.Etale} (f : W ⟶ U) (M : ModuleCat.{u + 1} R) :
    (Y.smallEtaleTopology.overMapPullback (ModuleCat.{u + 1} R) f).obj
        ((constantSheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)).obj M) ≅
      (constantSheaf (Y.smallEtaleTopology.over W) (ModuleCat.{u + 1} R)).obj M :=
  ((Over.map f).pushforwardContinuousSheafificationCompatibility (ModuleCat.{u + 1} R)
    (Y.smallEtaleTopology.over W) (Y.smallEtaleTopology.over U)).symm.app
      ((Functor.const (Over U)ᵒᵖ).obj M)

/-- The model of a given constant chart maps to the ambient stalk by its constant sections. -/
def modelToStalk (U : Y.Etale) (p : xbar.toSmallEtalePoint.fiber.obj U)
    (M : ModuleCat.{u + 1} R)
    (e : F.over U ≅ (constantSheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)).obj M) :
    M ⟶ (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj F :=
  (toSheafify (Y.smallEtaleTopology.over U)
      ((Functor.const (Over U)ᵒᵖ).obj M)).app (op (Over.mk (𝟙 U))) ≫
    e.inv.hom.app (op (Over.mk (𝟙 U))) ≫ xbar.toSmallEtalePoint.toPresheafFiber U p F.obj

/-- Realize a stalk homomorphism on a smaller neighborhood of a supplied finite constant chart. -/
def inverseGermOnChart [Finite R]
    (U : Y.Etale) (p : xbar.toSmallEtalePoint.fiber.obj U)
    (M : ModuleCat.{u + 1} R) [Module.Finite R M]
    (e : F.over U ≅ (constantSheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)).obj M)
    (h : (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj F →ₗ[R]
      (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj G) :
    (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj
      (ActualLinearSheafHom.obj Y R F G) := by
  let Φ := xbar.toSmallEtalePoint
  let Ψ := Φ.over p
  letI : HasColimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
    hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} (ModuleCat.{u + 1} R)
  letI : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1}
      (CategoryTheory.forget (ModuleCat.{u + 1} R))
  let g : M ⟶ (Ψ.sheafFiber (A := ModuleCat.{u + 1} R)).obj (G.over U) :=
    modelToStalk R xbar F U p M e ≫ ModuleCat.ofHom h ≫
      (GrothendieckTopology.Point.OverFiber.sheafObjIso Φ p G).inv
  let L := Ψ.linearLift (G.over U).obj M g
  let W := L.U.left
  let eW : F.over W ≅
      (constantSheaf (Y.smallEtaleTopology.over W) (ModuleCat.{u + 1} R)).obj M :=
    (Y.smallEtaleTopology.overMapPullback (ModuleCat.{u + 1} R) L.U.hom).mapIso e ≪≫
      constantRestrictionIso R L.U.hom M
  let a : F.over W ⟶ G.over W := eW.hom ≫
    ((constantSheafAdj (Y.smallEtaleTopology.over W) (ModuleCat.{u + 1} R)
      Over.mkIdTerminal).homEquiv M (G.over W)).symm L.map
  exact Φ.toPresheafFiber W L.point.val (ActualLinearSheafHom.obj Y R F G).obj a.hom

/-- The chart construction evaluates a local section germ by the specified stalk homomorphism. -/
theorem evaluate_inverseGermOnChart_germ [Finite R]
    (U : Y.Etale) (p : xbar.toSmallEtalePoint.fiber.obj U)
    (M : ModuleCat.{u + 1} R) [Module.Finite R M]
    (e : F.over U ≅ (constantSheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)).obj M)
    (h : (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj F →ₗ[R]
      (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj G)
    (V : Y.Etale) (q : xbar.toSmallEtalePoint.fiber.obj V) (s : F.obj.obj (op V)) :
    evaluate R xbar F G (inverseGermOnChart R xbar F G U p M e h)
        (xbar.toSmallEtalePoint.toPresheafFiber V q F.obj s) =
      h (xbar.toSmallEtalePoint.toPresheafFiber V q F.obj s) := sorry

variable [ConnectedSpace Y]
variable [hR : Finite R] [hF : Sheaf.IsFiniteTypeLocallyConstantModule F]

/-- Construct the inverse Hom germ on an actual finite constant chart containing the point. -/
def inverse
    (h : (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj F →ₗ[R]
      (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj G) :
    (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj
      (ActualLinearSheafHom.obj Y R F G) := by
  let c := Sheaf.pointedConstantChart xbar.toSmallEtalePoint
    (fun M : ModuleCat.{u + 1} R ↦ Module.Finite R M) F
  letI : Module.Finite R c.model := c.property
  exact inverseGermOnChart R xbar F G c.U c.point c.model c.iso h

/-- Evaluation of the constructed inverse returns the given stalk homomorphism. -/
theorem map_inverse
    (h : (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj F →ₗ[R]
      (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj G) :
    map R xbar F G (inverse R xbar F G h) = h := sorry

/-- The constructed inverse returns the original local-Hom germ after evaluation. -/
theorem inverse_map
    (α : (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj
      (ActualLinearSheafHom.obj Y R F G)) :
    inverse R xbar F G (map R xbar F G α) = α := sorry

include hR hF in
/-- Local finite presentation makes the specified Hom/stalk map bijective.
Finite local constancy is essential; no assertion is made for arbitrary F. -/
theorem map_bijective : Function.Bijective (map R xbar F G) := sorry

def equiv : (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj
    (ActualLinearSheafHom.obj Y R F G) ≃ₗ[R]
    ((xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj F →ₗ[R]
        (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj G) :=
  { map R xbar F G with
    invFun := inverse R xbar F G
    left_inv := inverse_map R xbar F G
    right_inv := map_inverse R xbar F G }

/-- The forward direction of the equivalence is the original germ-evaluation map. -/
@[simp]
theorem equiv_apply
    (α : (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj
      (ActualLinearSheafHom.obj Y R F G)) :
    equiv R xbar F G α = map R xbar F G α := rfl

/-- The reverse direction is the actual finite-chart construction. -/
@[simp]
theorem equiv_symm_apply
    (h : (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj F →ₗ[R]
      (xbar.toSmallEtalePoint.sheafFiber (A := ModuleCat.{u + 1} R)).obj G) :
    (equiv R xbar F G).symm h = inverse R xbar F G h := rfl

end ActualLinearHomStalk
