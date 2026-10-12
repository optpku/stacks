/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap76.Lemma_76_52_4_Relative
public import stacks_project.Chap76.Lemma_76_52_8_DerivedHom

/-!
# Colimits of categories of relatively perfect objects on algebraic spaces

The category at each stage is the full subcategory cut out by
`ModuleDerived.perfectOver` for the corresponding relative structure morphism.
The category-colimit assertion is expressed operationally by descent of objects up to
isomorphism and by the canonical filtered-colimit property for morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The object property of being pseudo-coherent over `𝒪_X` and locally of finite Tor
dimension after restriction to `f⁻¹𝒪_Y`, without requiring flatness or local finite
presentation of `f`. -/
def perfectOver (f : X ⟶ Y) : ObjectProperty (ModuleDerived X) :=
  (fun E ↦ IsPseudoCoherent X E) ⊓ locallyFiniteTorDimensionOver f

/-- When `f` is flat and locally of finite presentation, `perfectOver f` agrees with
the source `Y`-perfect owner `perfectRelativeTo f`. -/
theorem perfectOver_eq_perfectRelativeTo (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] :
    perfectOver f = perfectRelativeTo f := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived

namespace AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S}
variable [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsQuasiSeparated (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]

/-- The relative structure morphism from a base-changed stage to its stage of the base
diagram. -/
noncomputable abbrev stageRelative
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    (baseChangeOverDiagram D (OrderDual.toDual s.base) x₀).obj j.unop ⟶
      D.obj j.unop.left :=
  pullback.fst (D.map j.unop.hom) x₀

/-- The stage-relative morphism forms the canonical pullback square. -/
theorem stageRelative_comp
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    s.stageRelative x₀ j ≫ D.map j.unop.hom =
      pullback.snd (D.map j.unop.hom) x₀ ≫ x₀ := sorry

/-- The relative structure morphism from the base-changed limit to the limiting algebraic
space. -/
noncomputable abbrev limitRelative
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base)) :
    (baseChangeOverCone D s.limitCone.cone
      (OrderDual.toDual s.base) x₀).pt ⟶ (s.limitCone.cone).pt :=
  pullback.fst (s.limitCone.cone.π.app (OrderDual.toDual s.base)) x₀

/-- The limit-relative morphism forms the canonical pullback square. -/
theorem limitRelative_comp
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base)) :
    s.limitRelative x₀ ≫
        s.limitCone.cone.π.app (OrderDual.toDual s.base) =
      pullback.snd
          (s.limitCone.cone.π.app (OrderDual.toDual s.base)) x₀ ≫ x₀ := sorry

/-- The canonical morphism from the base-changed limit to a stage in the cofinal tail. -/
noncomputable abbrev limitToStage
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    (baseChangeOverCone D s.limitCone.cone
      (OrderDual.toDual s.base) x₀).pt ⟶
      (baseChangeOverDiagram D (OrderDual.toDual s.base) x₀).obj j.unop :=
  (baseChangeOverCone D s.limitCone.cone
    (OrderDual.toDual s.base) x₀).π.app j.unop

/-- The limit-to-stage morphism commutes with the relative structure morphisms. -/
theorem limitToStage_relative
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    s.limitToStage x₀ j ≫ s.stageRelative x₀ j =
      s.limitRelative x₀ ≫ s.limitCone.cone.π.app j.unop.left := sorry

/-- The operational category-colimit property for relative-perfect complexes: every
relative-perfect object on the base-changed limit descends, up to isomorphism, from a
relative-perfect object at a stage, and at every stage the canonical diagram of morphism
types between arbitrary relative-perfect objects is a filtered colimit. -/
def IsPerfectOverCategoryColimit
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base)) : Prop :=
  (∀ (K : (ModuleDerived.perfectOver (s.limitRelative x₀)).FullSubcategory),
      ∃ (j : (Over (OrderDual.toDual s.base))ᵒᵖ)
          (Kj : (ModuleDerived.perfectOver
            (s.stageRelative x₀ j)).FullSubcategory),
        IsIsomorphic K.obj
          ((ModuleDerived.pullback (s.limitToStage x₀ j)).obj Kj.obj)) ∧
    ∀ (j : (Over (OrderDual.toDual s.base))ᵒᵖ)
      (Kⱼ Lⱼ : (ModuleDerived.perfectOver
        (s.stageRelative x₀ j)).FullSubcategory),
      Nonempty (IsColimit
        ((s.withBase (OrderDual.ofDual j.unop.left)).homDiagram
          (s.stageRelative x₀ j) Kⱼ.obj Lⱼ.obj).cocone)

namespace IsPerfectOverCategoryColimit

/-- The object-descent clause and the all-stage morphism-colimit clause defining the
operational relative-perfect category colimit. -/
theorem spec
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base)) :
    s.IsPerfectOverCategoryColimit x₀ ↔
      ((∀ (K : (ModuleDerived.perfectOver (s.limitRelative x₀)).FullSubcategory),
          ∃ (j : (Over (OrderDual.toDual s.base))ᵒᵖ)
              (Kj : (ModuleDerived.perfectOver
                (s.stageRelative x₀ j)).FullSubcategory),
            IsIsomorphic K.obj
              ((ModuleDerived.pullback (s.limitToStage x₀ j)).obj Kj.obj)) ∧
        ∀ (j : (Over (OrderDual.toDual s.base))ᵒᵖ)
          (Kⱼ Lⱼ : (ModuleDerived.perfectOver
            (s.stageRelative x₀ j)).FullSubcategory),
          Nonempty (IsColimit
            ((s.withBase (OrderDual.ofDual j.unop.left)).homDiagram
              (s.stageRelative x₀ j) Kⱼ.obj Lⱼ.obj).cocone)) := sorry

/-- A relative-perfect object on the limit descends from a relative-perfect object at some
stage, up to isomorphism after derived pullback. -/
theorem exists_stage
    {s : QcqsAffineLimit D} {X₀ : AlgebraicSpace S}
    {x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base)}
    (h : s.IsPerfectOverCategoryColimit x₀)
    (K : (ModuleDerived.perfectOver (s.limitRelative x₀)).FullSubcategory) :
    ∃ (j : (Over (OrderDual.toDual s.base))ᵒᵖ)
        (Kj : (ModuleDerived.perfectOver
          (s.stageRelative x₀ j)).FullSubcategory),
      IsIsomorphic K.obj
        ((ModuleDerived.pullback (s.limitToStage x₀ j)).obj Kj.obj) := sorry

/-- At every stage, the canonical Hom diagram for two arbitrary relative-perfect objects is
a filtered colimit after rebasing the specified limiting cone at that stage. -/
theorem hom_isColimit
    {s : QcqsAffineLimit D} {X₀ : AlgebraicSpace S}
    {x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base)}
    (h : s.IsPerfectOverCategoryColimit x₀)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ)
    (Kⱼ Lⱼ : (ModuleDerived.perfectOver
      (s.stageRelative x₀ j)).FullSubcategory) :
    Nonempty (IsColimit
      ((s.withBase (OrderDual.ofDual j.unop.left)).homDiagram
        (s.stageRelative x₀ j) Kⱼ.obj Lⱼ.obj).cocone) := sorry

end IsPerfectOverCategoryColimit

/-- For a flat finitely presented base change of a qcqs affine limit, relative-perfect
objects and their morphisms satisfy the operational filtered-category-colimit property. -/
theorem isPerfectOverCategoryColimit
    (s : QcqsAffineLimit D) (X₀ : AlgebraicSpace S)
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    [Flat x₀] [FinitePresentation x₀] :
    s.IsPerfectOverCategoryColimit x₀ := sorry

end AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit
