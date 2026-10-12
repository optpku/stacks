/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.HomDiagram
public import stacks_project.Chap70.Situation_70_5_5_QcqsAffine
public import stacks_project.Chap75.Lemma_75_26_6_Pullback

/-!
# Derived Hom diagrams for qcqs affine limits of algebraic spaces

This module constructs the direct stage and limiting derived pullbacks, together with
the canonical filtered diagram of their Hom types.
-/

public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit.DerivedHom

/-- The canonical comparison from iterated derived pullback to derived pullback along the
composite morphism is invertible. -/
private theorem pullbackCompComparison_isIso {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ Z) (g : Z ⟶ X) :
    IsIso (ModuleDerived.pullbackCompComparison f g) :=
  sorry

/-- Upgrade the derived-pullback composition comparison to an isomorphism. -/
private noncomputable def pullbackCompIso {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ Z) (g : Z ⟶ X) :
    ModuleDerived.pullback g ⋙ ModuleDerived.pullback f ≅
      ModuleDerived.pullback (f ≫ g) :=
  @asIso _ _ _ _ (ModuleDerived.pullbackCompComparison f g)
    (pullbackCompComparison_isIso f g)

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S}
variable [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsQuasiSeparated (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]

/-- The projection from a stage in the cofinal tail to the distinguished base stage. -/
private noncomputable abbrev stageProjection
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    D.obj j.unop.left ⟶ D.obj (OrderDual.toDual s.base) :=
  D.map j.unop.hom

/-- The transition morphism associated to a morphism in the opposite cofinal tail. -/
private noncomputable abbrev stageTransition
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    {j k : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k) :
    D.obj k.unop.left ⟶ D.obj j.unop.left :=
  D.map f.unop.left

/-- The limiting cone projection to the distinguished base stage. -/
private noncomputable abbrev limitProjection
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D) :
    s.limitCone.cone.pt ⟶ D.obj (OrderDual.toDual s.base) :=
  s.limitCone.cone.π.app (OrderDual.toDual s.base)

/-- Derived pullback from the distinguished stage to a stage in the cofinal tail. -/
noncomputable def stagePullback
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    ModuleDerived (D.obj (OrderDual.toDual s.base)) ⥤
      ModuleDerived (D.obj j.unop.left) :=
  ModuleDerived.pullback (stageProjection s j)

/-- The value of `stagePullback` is the canonical derived pullback along the stage projection. -/
theorem stagePullback_obj
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ)
    (E₀ : ModuleDerived (D.obj (OrderDual.toDual s.base))) :
    (stagePullback s j).obj E₀ =
      (ModuleDerived.pullback (D.map j.unop.hom)).obj E₀ :=
  sorry

/-- Derived pullback from the distinguished stage to the specified limiting algebraic space. -/
noncomputable def limitPullback
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D) :
    ModuleDerived (D.obj (OrderDual.toDual s.base)) ⥤
      ModuleDerived s.limitCone.cone.pt :=
  ModuleDerived.pullback (limitProjection s)

/-- The value of `limitPullback` is the canonical derived pullback along the limiting
cone projection. -/
theorem limitPullback_obj
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    (E₀ : ModuleDerived (D.obj (OrderDual.toDual s.base))) :
    (limitPullback s).obj E₀ =
      (ModuleDerived.pullback
        (s.limitCone.cone.π.app (OrderDual.toDual s.base))).obj E₀ :=
  sorry

/-- Derived pullback along a transition followed by the stage projection agrees with
direct pullback from the distinguished stage. -/
private theorem stagePullback_comp_eq
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    {j k : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k) :
    ModuleDerived.pullback ((stageTransition s f) ≫ stageProjection s j) =
      stagePullback s k :=
  sorry

/-- Derived pullback through a stage agrees with direct pullback to the limit. -/
private theorem limitPullback_comp_eq
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    ModuleDerived.pullback
        (s.limitCone.cone.π.app j.unop.left ≫ stageProjection s j) =
      limitPullback s :=
  sorry

/-- The canonical comparison between iterated pullback along a stage transition and
direct pullback from the distinguished stage. -/
private noncomputable def stagePullbackCompIso
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    {j k : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k) :
    stagePullback s j ⋙ ModuleDerived.pullback (stageTransition s f) ≅
      stagePullback s k :=
  pullbackCompIso (stageTransition s f) (stageProjection s j) ≪≫
    eqToIso (stagePullback_comp_eq s f)

/-- The canonical comparison between pullback through a stage and direct pullback to
the limiting algebraic space. -/
private noncomputable def limitPullbackCompIso
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    stagePullback s j ⋙
        ModuleDerived.pullback (s.limitCone.cone.π.app j.unop.left) ≅
      limitPullback s :=
  pullbackCompIso (s.limitCone.cone.π.app j.unop.left) (stageProjection s j) ≪≫
    eqToIso (limitPullback_comp_eq s j)

/-- Pull a morphism between stage derived pullbacks along a transition in the cofinal tail. -/
noncomputable def stageHomMap
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    (E₀ K₀ : ModuleDerived (D.obj (OrderDual.toDual s.base)))
    {j k : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k) :
    ((stagePullback s j).obj E₀ ⟶ (stagePullback s j).obj K₀) →
      ((stagePullback s k).obj E₀ ⟶ (stagePullback s k).obj K₀) :=
  fun β ↦
    (stagePullbackCompIso s f).inv.app E₀ ≫
      (ModuleDerived.pullback (stageTransition s f)).map β ≫
      (stagePullbackCompIso s f).hom.app K₀

/-- The stage Hom transition associated to an identity is the identity function. -/
theorem stageHomMap_id
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    (E₀ K₀ : ModuleDerived (D.obj (OrderDual.toDual s.base)))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    stageHomMap s E₀ K₀ (𝟙 j) =
      𝟙 ((stagePullback s j).obj E₀ ⟶ (stagePullback s j).obj K₀) :=
  sorry

/-- Stage Hom transitions respect composition. -/
theorem stageHomMap_comp
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    (E₀ K₀ : ModuleDerived (D.obj (OrderDual.toDual s.base)))
    {j k l : (Over (OrderDual.toDual s.base))ᵒᵖ}
    (f : j ⟶ k) (g : k ⟶ l) :
    stageHomMap s E₀ K₀ (f ≫ g) =
      Function.comp (stageHomMap s E₀ K₀ g) (stageHomMap s E₀ K₀ f) :=
  sorry

/-- The identity law in the categorical `Type` morphism wrapper. -/
theorem stageHomMap_id_cat
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    (E₀ K₀ : ModuleDerived (D.obj (OrderDual.toDual s.base)))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    TypeCat.ofHom (stageHomMap s E₀ K₀ (𝟙 j)) = 𝟙 _ :=
  sorry

/-- The composition law in the categorical `Type` morphism wrapper. -/
theorem stageHomMap_comp_cat
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    (E₀ K₀ : ModuleDerived (D.obj (OrderDual.toDual s.base)))
    {j k l : (Over (OrderDual.toDual s.base))ᵒᵖ}
    (f : j ⟶ k) (g : k ⟶ l) :
    TypeCat.ofHom (stageHomMap s E₀ K₀ (f ≫ g)) =
      TypeCat.ofHom
        (Function.comp (stageHomMap s E₀ K₀ g) (stageHomMap s E₀ K₀ f)) :=
  sorry

/-- The concrete functor of Hom types between the direct stage derived pullbacks. -/
@[expose]
noncomputable def stageFunctor
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    (E₀ K₀ : ModuleDerived (D.obj (OrderDual.toDual s.base))) :
    (Over (OrderDual.toDual s.base))ᵒᵖ ⥤ Type _ where
  obj j := (stagePullback s j).obj E₀ ⟶ (stagePullback s j).obj K₀
  map f := TypeCat.ofHom (stageHomMap s E₀ K₀ f)
  map_id j := stageHomMap_id_cat s E₀ K₀ j
  map_comp f g := stageHomMap_comp_cat s E₀ K₀ f g

/-- The object value of the stage functor is the expected derived-category Hom type. -/
theorem stageFunctor_obj
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    (E₀ K₀ : ModuleDerived (D.obj (OrderDual.toDual s.base)))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    (stageFunctor s E₀ K₀).obj j =
      ((stagePullback s j).obj E₀ ⟶ (stagePullback s j).obj K₀) :=
  sorry

/-- The map of the stage functor is the canonical derived-pullback transition. -/
theorem stageFunctor_map
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    (E₀ K₀ : ModuleDerived (D.obj (OrderDual.toDual s.base)))
    {j k : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k) :
    (stageFunctor s E₀ K₀).map f = TypeCat.ofHom (stageHomMap s E₀ K₀ f) :=
  sorry

/-- Pull a stage morphism to the limiting algebraic space along the corresponding cone
projection. -/
noncomputable def stageToLimit
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    (E₀ K₀ : ModuleDerived (D.obj (OrderDual.toDual s.base)))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    ((stagePullback s j).obj E₀ ⟶ (stagePullback s j).obj K₀) →
      ((limitPullback s).obj E₀ ⟶ (limitPullback s).obj K₀) :=
  fun β ↦
    (limitPullbackCompIso s j).inv.app E₀ ≫
      (ModuleDerived.pullback (s.limitCone.cone.π.app j.unop.left)).map β ≫
      (limitPullbackCompIso s j).hom.app K₀

/-- The stage-to-limit Hom maps commute with the transition maps. -/
theorem stageToLimit_natural
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    (E₀ K₀ : ModuleDerived (D.obj (OrderDual.toDual s.base)))
    {j k : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k)
    (β : (stageFunctor s E₀ K₀).obj j) :
    stageToLimit s E₀ K₀ k ((stageFunctor s E₀ K₀).map f β) =
      stageToLimit s E₀ K₀ j β :=
  sorry

/-- Naturality in the bundled form required by the filtered Hom diagram. -/
private theorem diagram_natural
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    (E₀ K₀ : ModuleDerived (D.obj (OrderDual.toDual s.base))) :
    ∀ ⦃j k : (Over (OrderDual.toDual s.base))ᵒᵖ⦄ (f : j ⟶ k)
      (β : (stageFunctor s E₀ K₀).obj j),
      stageToLimit s E₀ K₀ k ((stageFunctor s E₀ K₀).map f β) =
        stageToLimit s E₀ K₀ j β :=
  sorry

/-- The canonical filtered Hom diagram for the direct cofinal tail and its limit. -/
noncomputable def diagram
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    (E₀ K₀ : ModuleDerived (D.obj (OrderDual.toDual s.base))) :
    DerivedCategory.FilteredColimit.HomDiagram
      (stageFunctor s E₀ K₀)
      ((limitPullback s).obj E₀ ⟶ (limitPullback s).obj K₀) :=
  { ι := stageToLimit s E₀ K₀
    natural := diagram_natural s E₀ K₀ }

/-- Each cocone leg of `diagram` is the canonical stage-to-limit Hom map. -/
theorem diagram_ι
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    (E₀ K₀ : ModuleDerived (D.obj (OrderDual.toDual s.base)))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    (diagram s E₀ K₀).ι j = stageToLimit s E₀ K₀ j :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit.DerivedHom
