/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback.OverMap
public import ReasLib.AlgebraicGeometry.Scheme.OverField.StableContraction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Stable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.Point
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.HigherDirectImage

/-!
# Global contraction of a prestable family of curves to a stable family

A prestable family of curves of genus at least two over a scheme admits a
factorization through a stable family, unique up to unique isomorphism over
the base. The morphism of total spaces is a cohomological contraction after
every base change, and on residue-field fibres it is a stable contraction.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The field-valued point of `S` given by `Spec κ(s) ⟶ S`. -/
def residueFieldPoint {S : Scheme.{u}} (s : S) :
    FieldValuedPoint (ofOver (Over.mk (𝟙 S))) :=
  FieldValuedPoint.of (S.residueField s) (S.fromSpecResidueField s) (residueFieldHom S s)

/-- The morphism of `residueFieldPoint s` into `S` is `residueFieldHom S s`. -/
theorem residueFieldPoint_hom {S : Scheme.{u}} (s : S) :
    (residueFieldPoint s).hom = residueFieldHom S s :=
  rfl

/-- The residue-field fibre of `f` at `s` is the field-valued fibre over
`residueFieldPoint s`. -/
theorem fiber_eq_fieldFiber {S : Scheme.{u}} {X : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S))) (s : S) :
    fiber f s = fieldFiber f (residueFieldPoint s) :=
  rfl

/-- The residue-field fibre of `f` at `s`, viewed as a scheme over `κ(s)`
after a representing isomorphism. -/
def residueFibreScheme {S : Scheme.{u}} {X : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S))) (s : S) (T : Over S)
    (e : fiber f s ≅ ofOver T) :
    SchemeOverField (S.residueField s) :=
  ofFibreScheme (residueFieldPoint s) T e

/-- The underlying scheme of `residueFibreScheme f s T e` is the representing
scheme `T`. -/
theorem residueFibreScheme_left {S : Scheme.{u}} {X : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S))) (s : S) (T : Over S)
    (e : fiber f s ≅ ofOver T) :
    (residueFibreScheme f s T e).left = T.left :=
  rfl

/-- The structure morphism of `residueFibreScheme f s T e` is the scheme
morphism underlying the comparison of `T` with `Spec κ(s)` over `S`. -/
theorem residueFibreScheme_hom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S))) (s : S) (T : Over S)
    (e : fiber f s ≅ ofOver T) :
    (residueFibreScheme f s T e).hom =
      (yonedaEquiv
          (e.inv ≫ fieldFiberToSpec f (residueFieldPoint s) :
            yoneda.obj T ⟶ yoneda.obj (residueFieldPoint s).overObj)).left :=
  rfl

/-- The scheme morphism of residue-field fibres induced by `c` commutes with
the structure morphisms to `Spec κ(s)`. -/
theorem fiberSchemeHom_over {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ ofOver (Over.mk (𝟙 S))} {q : Y ⟶ ofOver (Over.mk (𝟙 S))}
    (c : X ⟶ Y) (hc : c ≫ q = f) (s : S) {TX TY : Over S}
    (eX : fiber f s ≅ ofOver TX) (eY : fiber q s ≅ ofOver TY) :
    (yonedaEquiv
          (eX.inv ≫ fiberMap c hc s ≫ eY.hom :
            yoneda.obj TX ⟶ yoneda.obj TY)).left ≫
        (residueFibreScheme q s TY eY).hom =
      (residueFibreScheme f s TX eX).hom := by
  have hcomp :
      (eX.inv ≫ fiberMap c hc s ≫ eY.hom) ≫
          (eY.inv ≫ fieldFiberToSpec q (residueFieldPoint s)) =
        eX.inv ≫ fieldFiberToSpec f (residueFieldPoint s) := by
    calc
      _ = eX.inv ≫ fiberMap c hc s ≫ fieldFiberToSpec q (residueFieldPoint s) := by
        convert (congrArg (fun k : fiber q s ⟶ fiber q s ↦
            eX.inv ≫ fiberMap c hc s ≫ k ≫ fieldFiberToSpec q (residueFieldPoint s))
            eY.hom_inv_id) using 1 <;> rfl
      _ = _ := congrArg (eX.inv ≫ ·) (overMap_snd c hc (residueFieldHom S s))
  change
    (Yoneda.fullyFaithful.preimage (eX.inv ≫ fiberMap c hc s ≫ eY.hom) ≫
      Yoneda.fullyFaithful.preimage
        (eY.inv ≫ fieldFiberToSpec q (residueFieldPoint s))).left =
      (Yoneda.fullyFaithful.preimage
        (eX.inv ≫ fieldFiberToSpec f (residueFieldPoint s))).left
  rw [← Yoneda.fullyFaithful.preimage_comp]
  exact congrArg (fun k : yoneda.obj TX ⟶ yoneda.obj (residueFieldPoint s).overObj ↦
    (Yoneda.fullyFaithful.preimage k).left) hcomp

/-- The morphism of residue-field fibres induced by `c`, as a morphism of
schemes over `κ(s)` after choosing representing isomorphisms. -/
def fiberSchemeHom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ ofOver (Over.mk (𝟙 S))} {q : Y ⟶ ofOver (Over.mk (𝟙 S))}
    (c : X ⟶ Y) (hc : c ≫ q = f) (s : S) {TX TY : Over S}
    (eX : fiber f s ≅ ofOver TX) (eY : fiber q s ≅ ofOver TY) :
    residueFibreScheme f s TX eX ⟶ residueFibreScheme q s TY eY :=
  Over.homMk
    (yonedaEquiv
        (eX.inv ≫ fiberMap c hc s ≫ eY.hom :
          yoneda.obj TX ⟶ yoneda.obj TY)).left
    (fiberSchemeHom_over c hc s eX eY)

/-- The underlying scheme morphism of `fiberSchemeHom` is the Yoneda transpose
of the algebraic-space fibre map of `c`. -/
theorem fiberSchemeHom_left {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ ofOver (Over.mk (𝟙 S))} {q : Y ⟶ ofOver (Over.mk (𝟙 S))}
    (c : X ⟶ Y) (hc : c ≫ q = f) (s : S) {TX TY : Over S}
    (eX : fiber f s ≅ ofOver TX) (eY : fiber q s ≅ ofOver TY) :
    (fiberSchemeHom c hc s eX eY).left =
      (yonedaEquiv
          (eX.inv ≫ fiberMap c hc s ≫ eY.hom :
            yoneda.obj TX ⟶ yoneda.obj TY)).left :=
  rfl

/-- A morphism `c : X ⟶ Y` over `S` is a contraction of a prestable family
onto a stable family if `Y ⟶ S` is a stable family of curves, the unit
`𝒪_Y ⟶ c_* 𝒪_X` is an isomorphism with vanishing `R¹ c_* 𝒪_X` after every
base change of `S`, and every residue-field fibre of `c` is a stable
contraction of rational tails and bridges. -/
structure IsContractionToStable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ ofOver (Over.mk (𝟙 S))} {q : Y ⟶ ofOver (Over.mk (𝟙 S))}
    (c : X ⟶ Y) (hc : c ≫ q = f) : Prop where
  /-- The target morphism is a family of curves. -/
  isFamily : IsFamily q
  /-- The target morphism is a stable family of curves. -/
  isStableFamily : IsStableFamily q
  /-- After every base change `S' ⟶ S`, the unit `𝒪 ⟶ c_* 𝒪` is an
  isomorphism. -/
  universally_unit :
    ∀ {S' : Scheme.{u}} (σ : S' ⟶ S),
      IsIso (Modules.unitToPushforwardObjUnit
        (overMap c hc (ofOverHomMk σ (Category.comp_id _))))
  /-- After every base change `S' ⟶ S`, the first higher direct image of
  `𝒪` along `c` vanishes. -/
  universally_R1 :
    ∀ {S' : Scheme.{u}} (σ : S' ⟶ S),
      IsZero (higherDirectImageOne
        (overMap c hc (ofOverHomMk σ (Category.comp_id _))))
  /-- Every residue-field fibre of the source family is a scheme. -/
  source_fibre_isScheme : ∀ s : S, IsScheme (fiber f s)
  /-- Every representing scheme morphism of a residue-field fibre of `c` is
  a stable contraction. -/
  fibres_stableContraction :
    ∀ (s : S) (TX TY : Over S) (eX : fiber f s ≅ ofOver TX)
      (eY : fiber q s ≅ ofOver TY),
      StableContraction (fiberSchemeHom c hc s eX eY)

namespace IsContractionToStable

/-- Pack the family, stability, universal cohomological, and fibrewise stable
contraction properties of `c` into `IsContractionToStable`. -/
def ofProperties {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ ofOver (Over.mk (𝟙 S))} {q : Y ⟶ ofOver (Over.mk (𝟙 S))}
    (c : X ⟶ Y) (hc : c ≫ q = f) (isFamily : IsFamily q)
    (isStableFamily : IsStableFamily q)
    (universally_unit :
      ∀ {S' : Scheme.{u}} (σ : S' ⟶ S),
        IsIso (Modules.unitToPushforwardObjUnit
          (overMap c hc (ofOverHomMk σ (Category.comp_id _)))))
    (universally_R1 :
      ∀ {S' : Scheme.{u}} (σ : S' ⟶ S),
        IsZero (higherDirectImageOne
          (overMap c hc (ofOverHomMk σ (Category.comp_id _)))))
    (source_fibre_isScheme : ∀ s : S, IsScheme (fiber f s))
    (fibres_stableContraction :
      ∀ (s : S) (TX TY : Over S) (eX : fiber f s ≅ ofOver TX)
        (eY : fiber q s ≅ ofOver TY),
        StableContraction (fiberSchemeHom c hc s eX eY)) :
    IsContractionToStable c hc :=
  { isFamily, isStableFamily, universally_unit, universally_R1,
    source_fibre_isScheme, fibres_stableContraction }

/-- A contraction to a stable family is a stable family of curves on the
target, a universal cohomological contraction, and a stable contraction on
every represented residue-field fibre. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ ofOver (Over.mk (𝟙 S))} {q : Y ⟶ ofOver (Over.mk (𝟙 S))}
    {c : X ⟶ Y} {hc : c ≫ q = f} (h : IsContractionToStable c hc) :
    IsFamily q ∧ IsStableFamily q ∧
      (∀ {S' : Scheme.{u}} (σ : S' ⟶ S),
        IsIso (Modules.unitToPushforwardObjUnit
          (overMap c hc (ofOverHomMk σ (Category.comp_id _))))) ∧
      (∀ {S' : Scheme.{u}} (σ : S' ⟶ S),
        IsZero (higherDirectImageOne
          (overMap c hc (ofOverHomMk σ (Category.comp_id _))))) ∧
      (∀ s : S, IsScheme (fiber f s)) ∧
        ∀ (s : S) (TX TY : Over S) (eX : fiber f s ≅ ofOver TX)
          (eY : fiber q s ≅ ofOver TY),
          StableContraction (fiberSchemeHom c hc s eX eY) :=
  ⟨h.isFamily, h.isStableFamily, h.universally_unit, h.universally_R1,
    h.source_fibre_isScheme, h.fibres_stableContraction⟩

end IsContractionToStable

/-- A prestable family of curves of genus `g ≥ 2` factors through a stable
family of curves by a contraction to a stable family. -/
theorem exists_contractionToStable {S : Scheme.{u}} {X : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S))) {g : ℕ} (hg : 2 ≤ g)
    [IsFamily f] [Prestable f]
    (hgenus : SheafOfModules.IsFiniteLocallyFreeOfRank g (higherDirectImageOne f)) :
    ∃ (Y : AlgebraicSpace S) (q : Y ⟶ ofOver (Over.mk (𝟙 S)))
      (c : X ⟶ Y) (hc : c ≫ q = f), IsContractionToStable c hc := sorry

/-- A contraction of a prestable family of curves of genus `g ≥ 2` onto a
stable family is unique up to a unique isomorphism of targets over `S`
compatible with the contractions. -/
theorem contractionToStable_unique {S : Scheme.{u}} {X Y₁ Y₂ : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S)))
    (q₁ : Y₁ ⟶ ofOver (Over.mk (𝟙 S))) (q₂ : Y₂ ⟶ ofOver (Over.mk (𝟙 S)))
    {g : ℕ} (hg : 2 ≤ g) [IsFamily f] [Prestable f]
    (hgenus : SheafOfModules.IsFiniteLocallyFreeOfRank g (higherDirectImageOne f))
    (c₁ : X ⟶ Y₁) (hc₁ : c₁ ≫ q₁ = f) (c₂ : X ⟶ Y₂) (hc₂ : c₂ ≫ q₂ = f)
    (h₁ : IsContractionToStable c₁ hc₁) (h₂ : IsContractionToStable c₂ hc₂) :
    ∃! e : Y₁ ≅ Y₂, e.hom ≫ q₂ = q₁ ∧ c₁ ≫ e.hom = c₂ := sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
