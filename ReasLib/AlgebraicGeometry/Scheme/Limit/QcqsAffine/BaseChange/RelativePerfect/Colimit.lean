module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.QcqsAffine.BaseChange.DerivedHom.Colimit
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Relative

@[expose] public section

/-!
# Colimits of categories of relatively perfect objects

The category at each stage is the full subcategory cut out by
`RingedSpace.ModuleDerived.perfectOver` for the corresponding relative structure morphism.
The category-colimit assertion is expressed operationally by descent of objects up to
isomorphism and by the canonical filtered-colimit property for morphisms.
-/

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Limit.QcqsAffineLimit

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {D : OrderDual I ⥤ Scheme.{u}}
variable [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]

/-- The relative structure morphism from a base-changed stage to its stage of the base
diagram. -/
noncomputable abbrev stageRelative
    (s : QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    (Scheme.baseChangeOverDiagram D (OrderDual.toDual s.base) x₀).obj j.unop ⟶
      D.obj j.unop.left :=
  pullback.fst (D.map j.unop.hom) x₀

/-- The stage-relative morphism forms the canonical pullback square. -/
theorem stageRelative_comp
    (s : QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    s.stageRelative x₀ j ≫ D.map j.unop.hom =
      pullback.snd (D.map j.unop.hom) x₀ ≫ x₀ := sorry

/-- The relative structure morphism from the base-changed limit to the limiting scheme. -/
noncomputable abbrev limitRelative
    (s : QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base)) :
    (Scheme.baseChangeOverCone D s.limitCone.cone
      (OrderDual.toDual s.base) x₀).pt ⟶ (s.limitCone.cone).pt :=
  pullback.fst (s.limitCone.cone.π.app (OrderDual.toDual s.base)) x₀

/-- The limit-relative morphism forms the canonical pullback square. -/
theorem limitRelative_comp
    (s : QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base)) :
    s.limitRelative x₀ ≫
        s.limitCone.cone.π.app (OrderDual.toDual s.base) =
      pullback.snd
          (s.limitCone.cone.π.app (OrderDual.toDual s.base)) x₀ ≫ x₀ := sorry

/-- The canonical morphism from the base-changed limit to a stage in the cofinal tail. -/
noncomputable abbrev limitToStage
    (s : QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    (Scheme.baseChangeOverCone D s.limitCone.cone
      (OrderDual.toDual s.base) x₀).pt ⟶
      (Scheme.baseChangeOverDiagram D (OrderDual.toDual s.base) x₀).obj j.unop :=
  (Scheme.baseChangeOverCone D s.limitCone.cone
    (OrderDual.toDual s.base) x₀).π.app j.unop

/-- The limit-to-stage morphism commutes with the relative structure morphisms. -/
theorem limitToStage_relative
    (s : QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    s.limitToStage x₀ j ≫ s.stageRelative x₀ j =
      s.limitRelative x₀ ≫ s.limitCone.cone.π.app j.unop.left := sorry

/-- The operational category-colimit property for relative-perfect complexes: every
relative-perfect object on the base-changed limit descends, up to isomorphism, from a
relative-perfect object at a stage, and at every stage the canonical diagram of morphism
types between arbitrary relative-perfect objects is a filtered colimit. -/
def IsPerfectOverCategoryColimit
    (s : QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base)) : Prop :=
  (∀ (K : (RingedSpace.ModuleDerived.perfectOver
      (s.limitRelative x₀).toLRSHom.toShHom).FullSubcategory),
      ∃ (j : (Over (OrderDual.toDual s.base))ᵒᵖ)
          (Kj : (RingedSpace.ModuleDerived.perfectOver
            (s.stageRelative x₀ j).toLRSHom.toShHom).FullSubcategory),
        IsIsomorphic K.obj
          ((RingedSpace.modulePullbackDerived
            (s.limitToStage x₀ j).toLRSHom.toShHom).obj Kj.obj)) ∧
    ∀ (j : (Over (OrderDual.toDual s.base))ᵒᵖ)
      (Kⱼ Lⱼ : (RingedSpace.ModuleDerived.perfectOver
        (s.stageRelative x₀ j).toLRSHom.toShHom).FullSubcategory),
      Nonempty (IsColimit
        ((s.withBase (OrderDual.ofDual j.unop.left)).homDiagram
          (s.stageRelative x₀ j) Kⱼ.obj Lⱼ.obj).cocone)

namespace IsPerfectOverCategoryColimit

/-- The object-descent clause and the all-stage morphism-colimit clause defining the
operational relative-perfect category colimit. -/
theorem spec
    (s : QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base)) :
    s.IsPerfectOverCategoryColimit x₀ ↔
      ((∀ (K : (RingedSpace.ModuleDerived.perfectOver
          (s.limitRelative x₀).toLRSHom.toShHom).FullSubcategory),
          ∃ (j : (Over (OrderDual.toDual s.base))ᵒᵖ)
              (Kj : (RingedSpace.ModuleDerived.perfectOver
                (s.stageRelative x₀ j).toLRSHom.toShHom).FullSubcategory),
            IsIsomorphic K.obj
              ((RingedSpace.modulePullbackDerived
                (s.limitToStage x₀ j).toLRSHom.toShHom).obj Kj.obj)) ∧
        ∀ (j : (Over (OrderDual.toDual s.base))ᵒᵖ)
          (Kⱼ Lⱼ : (RingedSpace.ModuleDerived.perfectOver
            (s.stageRelative x₀ j).toLRSHom.toShHom).FullSubcategory),
          Nonempty (IsColimit
            ((s.withBase (OrderDual.ofDual j.unop.left)).homDiagram
              (s.stageRelative x₀ j) Kⱼ.obj Lⱼ.obj).cocone)) := sorry

/-- A relative-perfect object on the limit descends from a relative-perfect object at some
stage, up to isomorphism after derived pullback. -/
theorem exists_stage
    {s : QcqsAffineLimit D} {X₀ : Scheme.{u}}
    {x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base)}
    (h : s.IsPerfectOverCategoryColimit x₀)
    (K : (RingedSpace.ModuleDerived.perfectOver
      (s.limitRelative x₀).toLRSHom.toShHom).FullSubcategory) :
    ∃ (j : (Over (OrderDual.toDual s.base))ᵒᵖ)
        (Kj : (RingedSpace.ModuleDerived.perfectOver
          (s.stageRelative x₀ j).toLRSHom.toShHom).FullSubcategory),
      IsIsomorphic K.obj
        ((RingedSpace.modulePullbackDerived
          (s.limitToStage x₀ j).toLRSHom.toShHom).obj Kj.obj) := sorry

/-- At every stage, the canonical Hom diagram for two arbitrary relative-perfect objects is
a filtered colimit after rebasing the specified limiting cone at that stage. -/
theorem hom_isColimit
    {s : QcqsAffineLimit D} {X₀ : Scheme.{u}}
    {x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base)}
    (h : s.IsPerfectOverCategoryColimit x₀)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ)
    (Kⱼ Lⱼ : (RingedSpace.ModuleDerived.perfectOver
      (s.stageRelative x₀ j).toLRSHom.toShHom).FullSubcategory) :
    Nonempty (IsColimit
      ((s.withBase (OrderDual.ofDual j.unop.left)).homDiagram
        (s.stageRelative x₀ j) Kⱼ.obj Lⱼ.obj).cocone) := sorry

end IsPerfectOverCategoryColimit

/-- For a flat finitely presented base change of a qcqs affine limit, relative-perfect
objects and their morphisms satisfy the operational filtered-category-colimit property. -/
theorem isPerfectOverCategoryColimit
    (s : QcqsAffineLimit D) (X₀ : Scheme.{u})
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    [Flat x₀] [Scheme.Hom.FinitePresentation x₀] :
    s.IsPerfectOverCategoryColimit x₀ := sorry

end AlgebraicGeometry.Scheme.Limit.QcqsAffineLimit
