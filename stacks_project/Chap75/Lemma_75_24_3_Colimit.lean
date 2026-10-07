module

public import stacks_project.Chap70.Situation_70_5_5_QcqsAffine
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_24_2_DerivedHom

/-!
# Colimits of categories of perfect objects in qcqs affine limits of algebraic spaces

The category-colimit property is expressed operationally by descent of perfect objects up to
isomorphism and by the canonical filtered-colimit property for morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S}
variable [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsQuasiSeparated (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]

/-- The operational category-colimit property for perfect complexes: every perfect object on
the limit descends, up to isomorphism, from a perfect object at a stage, and the canonical
diagram of morphism types between stage objects is a filtered colimit. -/
def IsPerfectCategoryColimit (s : QcqsAffineLimit D) : Prop :=
  (∀ (E : ModuleDerived s.limitCone.cone.pt),
      ModuleDerived.IsPerfect E →
        ∃ (i : I) (Eᵢ : ModuleDerived (D.obj (OrderDual.toDual i))),
          ModuleDerived.IsPerfect Eᵢ ∧
            IsIsomorphic E
              ((ModuleDerived.pullback (s.limitCone.cone.π.app (OrderDual.toDual i))).obj
                Eᵢ)) ∧
    ∀ (i : I) (Eᵢ Kᵢ : ModuleDerived (D.obj (OrderDual.toDual i))),
      ModuleDerived.IsPerfect Eᵢ → ModuleDerived.IsPerfect Kᵢ →
        Nonempty (IsColimit (DerivedHom.diagram (withBase s i) Eᵢ Kᵢ).cocone)

namespace IsPerfectCategoryColimit

/-- Object descent and the morphism-colimit property characterize the operational colimit of
perfect categories. -/
theorem spec (s : QcqsAffineLimit D) :
    s.IsPerfectCategoryColimit ↔
      ((∀ (E : ModuleDerived s.limitCone.cone.pt),
          ModuleDerived.IsPerfect E →
            ∃ (i : I) (Eᵢ : ModuleDerived (D.obj (OrderDual.toDual i))),
              ModuleDerived.IsPerfect Eᵢ ∧
                IsIsomorphic E
                  ((ModuleDerived.pullback (s.limitCone.cone.π.app (OrderDual.toDual i))).obj
                    Eᵢ)) ∧
        ∀ (i : I) (Eᵢ Kᵢ : ModuleDerived (D.obj (OrderDual.toDual i))),
          ModuleDerived.IsPerfect Eᵢ → ModuleDerived.IsPerfect Kᵢ →
            Nonempty (IsColimit (DerivedHom.diagram (withBase s i) Eᵢ Kᵢ).cocone)) :=
  sorry

/-- A perfect object on the limit descends from a perfect object at some stage, up to
isomorphism after derived pullback. -/
theorem exists_stage {s : QcqsAffineLimit D} (h : s.IsPerfectCategoryColimit)
    (E : ModuleDerived s.limitCone.cone.pt) (hE : ModuleDerived.IsPerfect E) :
    ∃ (i : I) (Eᵢ : ModuleDerived (D.obj (OrderDual.toDual i))),
      ModuleDerived.IsPerfect Eᵢ ∧
        IsIsomorphic E
          ((ModuleDerived.pullback (s.limitCone.cone.π.app (OrderDual.toDual i))).obj Eᵢ) :=
  sorry

/-- The canonical derived Hom diagram for two perfect objects at a stage is a filtered
colimit. -/
theorem hom_isColimit {s : QcqsAffineLimit D} (h : s.IsPerfectCategoryColimit) (i : I)
    (Eᵢ Kᵢ : ModuleDerived (D.obj (OrderDual.toDual i)))
    (hE : ModuleDerived.IsPerfect Eᵢ) (hK : ModuleDerived.IsPerfect Kᵢ) :
    Nonempty (IsColimit (DerivedHom.diagram (withBase s i) Eᵢ Kᵢ).cocone) :=
  sorry

end IsPerfectCategoryColimit

/-- For a directed inverse limit of qcqs algebraic spaces with affine transition morphisms,
perfect objects and their morphisms satisfy the operational filtered-category-colimit
property. -/
theorem isPerfectCategoryColimit (s : QcqsAffineLimit D) :
    s.IsPerfectCategoryColimit :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit
