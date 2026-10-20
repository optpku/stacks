/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.IndexedCoproduct.HomFamily
public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Functor.Index
public import ReasLib.AlgebraicTopology.SimplicialSet.Pushout

/-!
# Simplicial copowers and pushouts

For a fixed simplicial object `X`, reindexing along a span of simplicial sets gives the canonical
copower cocone over that span's pushout.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe vC uC uS

namespace CategoryTheory.SimplicialObject.copower

variable {C : Type uC} [Category.{vC} C]
variable {U V W : SSet.{uS}} (a : U ⟶ V) (b : U ⟶ W) (X : SimplicialObject C)
variable [HasCopower U X] [HasCopower V X] [HasCopower W X]
variable [HasCopower (pushout a b) X]

namespace pushout

/-- Reindexing a fixed copower along the two composites into a simplicial-set pushout gives the
same morphism. -/
theorem condition :
    indexHom X a ≫ indexHom X (CategoryTheory.Limits.pushout.inl a b) =
      indexHom X b ≫ indexHom X (CategoryTheory.Limits.pushout.inr a b) := sorry

/-- The canonical copower cocone over a span of simplicial sets, with apex the copower indexed by
the simplicial-set pushout. -/
@[stacks 017N "copower pushout cocone"]
def cocone : PushoutCocone (indexHom X a) (indexHom X b) :=
  PushoutCocone.mk (indexHom X (CategoryTheory.Limits.pushout.inl a b))
    (indexHom X (CategoryTheory.Limits.pushout.inr a b)) (condition a b X)

namespace cocone

/-- The left leg of the canonical copower pushout cocone is reindexing by the left
coprojection. -/
@[simp]
theorem inl :
    (pushout.cocone a b X).inl =
      indexHom X (CategoryTheory.Limits.pushout.inl a b) := sorry

/-- The right leg of the canonical copower pushout cocone is reindexing by the right
coprojection. -/
@[simp]
theorem inr :
    (pushout.cocone a b X).inr =
      indexHom X (CategoryTheory.Limits.pushout.inr a b) := sorry

end cocone

namespace desc
namespace types

/-- The maps attached to the two representatives of a simplex in a pushout agree on each
representative coming from the source of the span. -/
theorem condition
    (s : PushoutCocone (indexHom X a) (indexHom X b))
    (Δ : SimplexCategoryᵒᵖ) (u : U.obj Δ) :
    Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) (a.app Δ u) ≫ s.inl.app Δ =
      Sigma.ι (fun _ : W.obj Δ ↦ X.obj Δ) (b.app Δ u) ≫ s.inr.app Δ := sorry

/-- The two summand families induced by a copower cocone respect the generating relation of the
explicit type-theoretic pushout. -/
theorem wellDefined
    (s : PushoutCocone (indexHom X a) (indexHom X b))
    (Δ : SimplexCategoryᵒᵖ) :
    ∀ z₁ z₂ : V.obj Δ ⊕ W.obj Δ,
      Types.Pushout.Rel (a.app Δ) (b.app Δ) z₁ z₂ →
        Sum.elim
            (fun v : V.obj Δ ↦ Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) v ≫ s.inl.app Δ)
            (fun w : W.obj Δ ↦ Sigma.ι (fun _ : W.obj Δ ↦ X.obj Δ) w ≫ s.inr.app Δ)
            z₁ =
          Sum.elim
            (fun v : V.obj Δ ↦ Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) v ≫ s.inl.app Δ)
            (fun w : W.obj Δ ↦ Sigma.ι (fun _ : W.obj Δ ↦ X.obj Δ) w ≫ s.inr.app Δ)
            z₂ := sorry

/-- The family of morphisms obtained by descending the two summand families to the explicit
type-theoretic pushout. -/
@[stacks 017N "type-theoretic copower pushout descent family"]
def family (s : PushoutCocone (indexHom X a) (indexHom X b))
    (Δ : SimplexCategoryᵒᵖ) :
    Types.Pushout (a.app Δ) (b.app Δ) → (X.obj Δ ⟶ s.pt.obj Δ) :=
  Quot.lift
    (fun z : V.obj Δ ⊕ W.obj Δ ↦
      Sum.elim
        (fun v : V.obj Δ ↦ Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) v ≫ s.inl.app Δ)
        (fun w : W.obj Δ ↦ Sigma.ι (fun _ : W.obj Δ ↦ X.obj Δ) w ≫ s.inr.app Δ)
        z)
    (wellDefined (a := a) (b := b) (X := X) s Δ)

namespace family

/-- The descended family evaluates on a left representative as the corresponding left cocone
leg after its coproduct injection. -/
@[simp]
theorem inl
    (s : PushoutCocone (indexHom X a) (indexHom X b))
    (Δ : SimplexCategoryᵒᵖ) (v : V.obj Δ) :
    types.family (a := a) (b := b) (X := X) s Δ
        (Types.Pushout.inl (a.app Δ) (b.app Δ) v) =
      Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) v ≫ s.inl.app Δ := sorry

/-- The descended family evaluates on a right representative as the corresponding right cocone
leg after its coproduct injection. -/
@[simp]
theorem inr
    (s : PushoutCocone (indexHom X a) (indexHom X b))
    (Δ : SimplexCategoryᵒᵖ) (w : W.obj Δ) :
    types.family (a := a) (b := b) (X := X) s Δ
        (Types.Pushout.inr (a.app Δ) (b.app Δ) w) =
      Sigma.ι (fun _ : W.obj Δ ↦ X.obj Δ) w ≫ s.inr.app Δ := sorry

end family
end types

/-- The compatible family on the simplicial-set pushout induced by a cocone of copower maps. Its
value is obtained by the universal map out of the degreewise pushout of types. -/
@[stacks 017N "copower pushout compatible family"]
def family (s : PushoutCocone (indexHom X a) (indexHom X b)) :
    Functor.indexedCoprod.HomFamily (CategoryTheory.Limits.pushout a b) X s.pt :=
  fun Δ z ↦
    types.family (a := a) (b := b) (X := X) s Δ
      ((SSet.evaluation.pushoutIso a b Δ).hom z)

namespace family

/-- The family induced on the simplicial-set pushout by a copower cocone is simplicially
compatible. -/
theorem isCompatible
    (s : PushoutCocone (indexHom X a) (indexHom X b)) :
    (desc.family (a := a) (b := b) (X := X) s).IsCompatible := sorry

end family

/-- The universal morphism from the pushout-indexed copower to the apex of a copower cocone. -/
@[stacks 017N "copower pushout descent"]
def hom (s : PushoutCocone (indexHom X a) (indexHom X b)) :
    copower (CategoryTheory.Limits.pushout a b) X ⟶ s.pt :=
  Functor.indexedCoprod.HomFamily.toHom
    ⟨family (a := a) (b := b) (X := X) s,
      family.isCompatible (a := a) (b := b) (X := X) s⟩

/-- The universal copower morphism restricts to the left leg of its target cocone. -/
theorem inl_hom
    (s : PushoutCocone (indexHom X a) (indexHom X b)) :
    indexHom X (CategoryTheory.Limits.pushout.inl a b) ≫ hom a b X s = s.inl := sorry

/-- The universal copower morphism restricts to the right leg of its target cocone. -/
theorem inr_hom
    (s : PushoutCocone (indexHom X a) (indexHom X b)) :
    indexHom X (CategoryTheory.Limits.pushout.inr a b) ≫ hom a b X s = s.inr := sorry

/-- A morphism out of the pushout-indexed copower is determined by its restrictions to the two
target legs of the indexing span. -/
theorem unique
    (s : PushoutCocone (indexHom X a) (indexHom X b))
    (m : copower (CategoryTheory.Limits.pushout a b) X ⟶ s.pt)
    (hV : indexHom X (CategoryTheory.Limits.pushout.inl a b) ≫ m = s.inl)
    (hW : indexHom X (CategoryTheory.Limits.pushout.inr a b) ≫ m = s.inr) :
    m = hom a b X s := sorry

end desc

/-- Copowering a fixed simplicial object sends a simplicial-set pushout to a pushout cocone. -/
@[stacks 017N "copower preserves pushouts"]
def isColimit : IsColimit (cocone a b X) :=
  PushoutCocone.IsColimit.mk (condition a b X)
    (desc.hom (a := a) (b := b) (X := X))
    (desc.inl_hom (a := a) (b := b) (X := X))
    (desc.inr_hom (a := a) (b := b) (X := X))
    (desc.unique (a := a) (b := b) (X := X))

end pushout

end CategoryTheory.SimplicialObject.copower
