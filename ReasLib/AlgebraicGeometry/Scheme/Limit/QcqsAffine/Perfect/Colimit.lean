/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.QcqsAffine.DerivedHom.Colimit
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Pullback

@[expose] public section

/-!
# Colimits of categories of perfect objects in qcqs affine limits

The category-colimit property is expressed operationally by descent of perfect objects up to
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

/-- The operational category-colimit property for perfect complexes: every perfect object on
the limit descends, up to isomorphism, from a perfect object at a stage, and the canonical
diagram of morphism types between stage objects is a filtered colimit. -/
def IsPerfectCategoryColimit (s : QcqsAffineLimit D) : Prop :=
  let c := s.limitCone.cone
  (∀ E : RingedSpace.ModuleDerived.Perfect (X := c.pt.toRingedSpace),
      ∃ (i : I) (Eᵢ : RingedSpace.ModuleDerived.Perfect
        (X := (D.obj (OrderDual.toDual i)).toRingedSpace)),
        IsIsomorphic E
          ((RingedSpace.modulePullbackPerfect
            (c.π.app (OrderDual.toDual i)).toLRSHom.toShHom).obj Eᵢ)) ∧
    ∀ (i : I)
        (Eᵢ Kᵢ : RingedSpace.ModuleDerived.Perfect
          (X := (D.obj (OrderDual.toDual i)).toRingedSpace)),
      Nonempty (IsColimit (DerivedHom.diagram (withBase s i) Eᵢ.obj Kᵢ.obj).cocone)

namespace IsPerfectCategoryColimit

/-- Object descent and the morphism-colimit property characterize the operational colimit of
perfect categories. -/
theorem spec (s : QcqsAffineLimit D) :
    s.IsPerfectCategoryColimit ↔
      let c := s.limitCone.cone
      ((∀ E : RingedSpace.ModuleDerived.Perfect (X := c.pt.toRingedSpace),
          ∃ (i : I) (Eᵢ : RingedSpace.ModuleDerived.Perfect
            (X := (D.obj (OrderDual.toDual i)).toRingedSpace)),
            IsIsomorphic E
              ((RingedSpace.modulePullbackPerfect
                (c.π.app (OrderDual.toDual i)).toLRSHom.toShHom).obj Eᵢ)) ∧
        ∀ (i : I)
            (Eᵢ Kᵢ : RingedSpace.ModuleDerived.Perfect
              (X := (D.obj (OrderDual.toDual i)).toRingedSpace)),
          Nonempty
            (IsColimit (DerivedHom.diagram (withBase s i) Eᵢ.obj Kᵢ.obj).cocone)) := sorry

/-- A perfect object on the limit descends from a perfect object at some stage, up to
isomorphism after derived pullback. -/
theorem exists_stage {s : QcqsAffineLimit D}
    (h : s.IsPerfectCategoryColimit)
    (E : RingedSpace.ModuleDerived.Perfect
      (X := s.limitCone.cone.pt.toRingedSpace)) :
    ∃ (i : I) (Eᵢ : RingedSpace.ModuleDerived.Perfect
      (X := (D.obj (OrderDual.toDual i)).toRingedSpace)),
      IsIsomorphic E
        ((RingedSpace.modulePullbackPerfect
          (s.limitCone.cone.π.app (OrderDual.toDual i)).toLRSHom.toShHom).obj Eᵢ) := sorry

/-- The canonical derived Hom diagram for two perfect objects at a stage is a filtered
colimit. -/
theorem hom_isColimit {s : QcqsAffineLimit D}
    (h : s.IsPerfectCategoryColimit) (i : I)
    (Eᵢ Kᵢ : RingedSpace.ModuleDerived.Perfect
      (X := (D.obj (OrderDual.toDual i)).toRingedSpace)) :
    Nonempty
      (IsColimit (DerivedHom.diagram (withBase s i) Eᵢ.obj Kᵢ.obj).cocone) := sorry

end IsPerfectCategoryColimit

/-- For a directed inverse limit of qcqs schemes with affine transition morphisms, perfect
objects and their morphisms satisfy the operational filtered-category-colimit property. -/
theorem isPerfectCategoryColimit (s : QcqsAffineLimit D) :
    s.IsPerfectCategoryColimit := sorry

end AlgebraicGeometry.Scheme.Limit.QcqsAffineLimit
