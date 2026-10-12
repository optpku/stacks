/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.EpiMono
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientPresheaf
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap68.Example_68_13_11_Presentation

/-!
# Quotient algebraic space of profinite translations

This module packages the quotient presheaf of the translation action on
`Spec(LocallyConstant G k)` as an algebraic space `X = Y / Γ` over `Spec(k)`, together
with the projection `q`, the origin `k`-point `x`, and the splitting of `x`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PreRelation
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation

/-- The algebraic space `X = Y / Γ` over `Spec(k)`, presented by left translations. -/
def X (k : Type u) [Field k] (G : ProfiniteGrp.{u}) : AlgebraicSpace (base k) where
  functorOfPoints := (ofAut (action k G)).quotientPresheaf
  isSheaf := sorry
  representableDiagonal := sorry
  atlas := ⟨YOver k G, (ofAut (action k G)).quotientMk, sorry, sorry⟩

/-- The functor of points of `X` is the objectwise quotient of `T`-points of `Y` by
translations. -/
theorem X_functorOfPoints (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    (X k G).functorOfPoints = (ofAut (action k G)).quotientPresheaf := sorry

/-- The atlas of `X` is the canonical projection to the quotient presheaf. -/
def atlasX (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    yoneda.obj (YOver k G) ⟶ (X k G).functorOfPoints :=
  (ofAut (action k G)).quotientMk

/-- The atlas of `X` is the quotient projection of the translation pre-relation. -/
theorem atlasX_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    atlasX k G = (ofAut (action k G)).quotientMk := sorry

/-- The algebraic space associated to `Y` is affine. -/
instance instIsAffine_ofOverY (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    AlgebraicSpace.IsAffine (ofOver (YOver k G)) :=
  inferInstance

/-- The algebraic space associated to `Y` is reduced. -/
instance instIsReduced_ofOverY (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    AlgebraicSpace.IsReduced (ofOver (YOver k G)) :=
  inferInstance

/-- The projection `q : Y ⟶ X` of algebraic spaces over `Spec(k)`. -/
def q (k : Type u) [Field k] (G : ProfiniteGrp.{u}) : ofOver (YOver k G) ⟶ X k G :=
  (ofAut (action k G)).quotientMk

/-- `q` is the quotient projection of the translation pre-relation. -/
theorem q_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    q k G = (ofAut (action k G)).quotientMk := sorry

/-- The `k`-point `x : Spec(k) ⟶ X` induced by the origin of `G`. -/
def x (k : Type u) [Field k] (G : ProfiniteGrp.{u}) : FieldValuedPoint (X k G) :=
  FieldValuedPoint.of k (𝟙 (base k)) (ofOverMap (originHom k G) ≫ q k G)

/-- The morphism of `x` is the composite of the origin with `q`. -/
theorem x_hom (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    (x k G).hom = ofOverMap (originHom k G) ≫ q k G := sorry

/-- The structure morphism of `x` is the identity of `Spec(k)`. -/
theorem x_structureHom (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    (x k G).structureHom = 𝟙 (base k) := sorry

/-- The point of `|X|` represented by the origin `k`-point. -/
def xPoint (k : Type u) [Field k] (G : ProfiniteGrp.{u}) : Points (X k G) :=
  Points.mk (x k G)

/-- `xPoint` is the class of the field-valued point `x`. -/
theorem xPoint_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    xPoint k G = Points.mk (x k G) := sorry

/-- The origin `k`-point is a section of `X ⟶ Spec(k)`. -/
theorem isSection_x (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    (x k G).hom ≫ toBase (X k G) = 𝟙 (ofOver (Over.mk (𝟙 (base k)))) := sorry

/-- The splitting of `x` by the structure morphism of `X`. -/
def splitMono_x (k : Type u) [Field k] (G : ProfiniteGrp.{u}) : SplitMono (x k G).hom where
  retraction := toBase (X k G)
  id := sorry

/-- The retraction of `splitMono_x` is the structure morphism of `X`. -/
theorem splitMono_x_retraction (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    (splitMono_x k G).retraction = toBase (X k G) := sorry


end AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation
