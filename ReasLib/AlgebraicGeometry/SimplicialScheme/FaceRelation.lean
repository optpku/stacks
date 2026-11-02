/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.SimplicialScheme.CechNerve
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation
public import ReasLib.AlgebraicTopology.Cech.Nerve.Projection
public import ReasLib.AlgebraicTopology.SimplicialObject.Cartesian

/-!
# Face pre-relation of a simplicial scheme over a morphism

The morphism `j = (Y.δ 1, Y.δ 0)` of a simplicial scheme `Y` over `f.simplicialScheme`
is recorded as a `Scheme.PreRelation` on `Y _⦋0⦌` over `S`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Simplicial
open Scheme.PreRelation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable {Y : SimplicialObject Scheme.{u}} (π : Y ⟶ f.simplicialScheme)

/-- The degree-`n` scheme of `Y` as an object of `Over S`, via `π` and the Čech-nerve
base projection of `f`. -/
def objOver (n : SimplexCategoryᵒᵖ) : Over S :=
  Over.mk (π.app n ≫ Arrow.cechNerve.base (Arrow.mk f) n)

/-- The structure morphism of `objOver f π n` is `π.app n` followed by the Čech-nerve
base projection. -/
theorem objOver_hom (n : SimplexCategoryᵒᵖ) :
    (objOver f π n).hom = π.app n ≫ Arrow.cechNerve.base (Arrow.mk f) n :=
  rfl

/-- Each face map `Y.δ i` is a morphism over `S`. -/
theorem face_comp_objOver (i : Fin 2) :
    Y.δ i ≫ (objOver f π (op ⦋0⦌)).hom = (objOver f π (op ⦋1⦌)).hom :=
  by
    change Y.δ i ≫ (π ≫ (Arrow.mk f).augmentedCechNerve.hom).app (op ⦋0⦌) =
      (π ≫ (Arrow.mk f).augmentedCechNerve.hom).app (op ⦋1⦌)
    exact ((π ≫ (Arrow.mk f).augmentedCechNerve.hom).naturality
      (SimplexCategory.δ i).op).trans (Category.comp_id _)

/-- The face map `Y.δ i` as a morphism of schemes over `S`. -/
def faceOver (i : Fin 2) :
    objOver f π (op ⦋1⦌) ⟶ objOver f π (op ⦋0⦌) :=
  Over.homMk (Y.δ i) (face_comp_objOver f π i)

/-- The underlying scheme morphism of `faceOver f π i` is `Y.δ i`. -/
theorem faceOver_left (i : Fin 2) :
    (faceOver f π i).left = Y.δ i :=
  rfl

/-- The pair `j = (Y.δ 1, Y.δ 0)` as a morphism over `S` into the product
`Y _⦋0⦌ ⨯_S Y _⦋0⦌`. -/
def facePair :
    objOver f π (op ⦋1⦌) ⟶ objOver f π (op ⦋0⦌) ⨯ objOver f π (op ⦋0⦌) :=
  prod.lift (faceOver f π 1) (faceOver f π 0)

/-- The first factor of `facePair f π` is the target face `Y.δ 1`. -/
theorem facePair_fst :
    facePair f π ≫ prod.fst = faceOver f π 1 :=
  prod.lift_fst _ _

/-- The second factor of `facePair f π` is the source face `Y.δ 0`. -/
theorem facePair_snd :
    facePair f π ≫ prod.snd = faceOver f π 0 :=
  prod.lift_snd _ _

/-- The two face maps `Y.δ 1` and `Y.δ 0` agree after composing with the structure map
of `Y _⦋0⦌` over `S`. -/
theorem facePair_comp :
    Y.δ (1 : Fin 2) ≫ (objOver f π (op ⦋0⦌)).hom =
      Y.δ (0 : Fin 2) ≫ (objOver f π (op ⦋0⦌)).hom :=
  (face_comp_objOver f π 1).trans (face_comp_objOver f π 0).symm

set_option backward.isDefEq.respectTransparency false in
/-- After identifying the product in `Over S` with the fibre product over `S`,
`facePair f π` recovers `j : Y _⦋1⦌ ⟶ Y _⦋0⦌ ×_S Y _⦋0⦌`. -/
theorem facePair_left :
    (facePair f π).left ≫
      (Over.prodLeftIsoPullback
        (objOver f π (op ⦋0⦌)) (objOver f π (op ⦋0⦌))).hom =
      pullback.lift (Y.δ (1 : Fin 2)) (Y.δ (0 : Fin 2)) (facePair_comp f π) :=
  by
    apply pullback.hom_ext
    · rw [Category.assoc, Over.prodLeftIsoPullback_hom_fst, pullback.lift_fst,
        ← Over.comp_left, facePair_fst, faceOver_left]
    · rw [Category.assoc, Over.prodLeftIsoPullback_hom_snd, pullback.lift_snd,
        ← Over.comp_left, facePair_snd, faceOver_left]

/-- The pre-relation on `Y _⦋0⦌` over `S` with defining map `j = (Y.δ 1, Y.δ 0)`. -/
def facePreRelation : Scheme.PreRelation (objOver f π (op ⦋0⦌)) :=
  ofHom (facePair f π)

/-- The target projection of `facePreRelation f π` is the face `Y.δ 1`. -/
theorem facePreRelation_t :
    (facePreRelation f π).t = faceOver f π 1 :=
  facePair_fst f π

/-- The source projection of `facePreRelation f π` is the face `Y.δ 0`. -/
theorem facePreRelation_s :
    (facePreRelation f π).s = faceOver f π 0 :=
  facePair_snd f π

/-- The defining arrow of `facePreRelation f π` is `facePair f π`. -/
theorem facePreRelation_hom :
    (facePreRelation f π).hom = facePair f π :=
  rfl

/-- A cartesian morphism of simplicial schemes to the Čech nerve of a scheme morphism
makes the ordered pair of degree-one faces an equivalence relation over the base. -/
instance instIsEquivalenceRelation_facePreRelation [SimplicialObject.IsCartesian π] :
    IsEquivalenceRelation (facePreRelation f π).t (facePreRelation f π).s :=
  sorry

end AlgebraicGeometry.Scheme.Hom
