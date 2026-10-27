/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.FreeAbelianYoneda

/-!
# Universe-raised free abelian representables

This leaf supplies the free-abelian Yoneda API when a presheaf takes values in
a universe larger than the hom universe of its indexing category. It uses
`uliftYoneda`, rather than silently coercing a representable into a larger
universe.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory.FreeAbelianYoneda.ULift

variable {C : Type u} [Category.{v} C]

/-- The universe-raised free abelian Yoneda functor. -/
noncomputable abbrev functor : C ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{max w v} :=
  uliftYoneda.{w} ⋙ FreeAbelianPresheaf.functor

/-- The free abelian presheaf on the universe-raised representable at `U`. -/
@[stacks 03A7 "universe-raised representable"]
noncomputable abbrev obj (U : C) :
    Cᵒᵖ ⥤ AddCommGrpCat.{max w v} :=
  functor.obj U

/-- The universe-raised free abelian Yoneda morphism induced by `f`. -/
noncomputable abbrev map {U V : C} (f : U ⟶ V) : obj.{u, v, w} U ⟶ obj V :=
  functor.map f

/-- The universe-raised free abelian Yoneda functor preserves monomorphisms. -/
instance functor_preservesMonomorphisms :
    (functor (C := C)).PreservesMonomorphisms where
  preserves {U V} f _ := by
    haveI (X : Cᵒᵖ) : Mono ((functor.map f).app X) := by
      change Mono (AddCommGrpCat.free.map ((uliftYoneda.map f).app X))
      haveI : Mono ((uliftYoneda.map f).app X) := by
        rw [mono_iff_injective]
        intro a b h
        apply ULift.ext
        exact (cancel_mono f).1 (congrArg ULift.down h)
      infer_instance
    exact NatTrans.mono_of_mono_app _

/-- Morphisms from the universe-raised free abelian representable at `U` to `P` are equivalent
to sections of `P` over `U`. -/
@[stacks 03A8 "universe-raised representable"]
noncomputable def homEquiv
    (U : C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}) :
    (obj.{u, v, w} U ⟶ P) ≃ P.obj (op U) :=
  ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _).trans uliftYonedaEquiv

/-- The universe-raised free-abelian-representable Hom/sections equivalence evaluates a
morphism on the free generator corresponding to the lifted identity of `U`. -/
theorem homEquiv_apply
    (U : C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v})
    (α : obj.{u, v, w} U ⟶ P) :
    homEquiv U P α =
      α.app (op U) (FreeAbelianGroup.of (ULift.up (𝟙 U))) := by
  rfl

/-- The universe-raised free-abelian-representable Hom/sections equivalence commutes with
postcomposition in the target presheaf. -/
theorem homEquiv_comp
    {U : C} {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}}
    (α : obj.{u, v, w} U ⟶ P) (β : P ⟶ Q) :
    homEquiv U Q (α ≫ β) = β.app (op U) (homEquiv U P α) := by
  rw [homEquiv_apply, homEquiv_apply]
  rfl

/-- The universe-raised free-abelian-representable Hom/sections equivalence commutes with
restriction along a morphism of representing objects. -/
theorem homEquiv_naturality
    {U V : C} (f : U ⟶ V) (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v})
    (α : obj.{u, v, w} V ⟶ P) :
    homEquiv U P (map f ≫ α) = P.map f.op (homEquiv V P α) := by
  rw [homEquiv_apply, homEquiv_apply]
  change α.app (op U) (FreeAbelianGroup.of (ULift.up (𝟙 U ≫ f))) = _
  rw [Category.id_comp]
  have h := congrArg (fun k => k (FreeAbelianGroup.of (ULift.up (𝟙 V))))
    (α.naturality f.op)
  change α.app (op U) (FreeAbelianGroup.of (ULift.up (f ≫ 𝟙 V))) =
    P.map f.op (α.app (op V) (FreeAbelianGroup.of (ULift.up (𝟙 V)))) at h
  simpa only [Category.comp_id] using h

/-- The universe-raised free-abelian-representable Hom/sections equivalence is additive. -/
theorem homEquiv_add
    (U : C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v})
    (α β : obj.{u, v, w} U ⟶ P) :
    homEquiv U P (α + β) = homEquiv U P α + homEquiv U P β := by
  rw [homEquiv_apply, homEquiv_apply, homEquiv_apply]
  rfl

/-- Morphisms from the universe-raised free abelian representable at `U` identify additively
with sections over `U`. -/
@[stacks 03A8 "additive universe-raised representable"]
noncomputable def homAddEquiv
    (U : C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}) :
    (obj.{u, v, w} U ⟶ P) ≃+ P.obj (op U) where
  toEquiv := homEquiv U P
  map_add' := homEquiv_add U P

/-- The additive universe-raised free-abelian-representable Hom/sections equivalence evaluates
a morphism on the free generator corresponding to the lifted identity of `U`. -/
theorem homAddEquiv_apply
    (U : C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v})
    (α : obj.{u, v, w} U ⟶ P) :
    homAddEquiv U P α =
      α.app (op U) (FreeAbelianGroup.of (ULift.up (𝟙 U))) := by
  exact homEquiv_apply U P α

/-- The additive universe-raised free-abelian-representable Hom/sections equivalence commutes
with restriction along a morphism of representing objects. -/
theorem homAddEquiv_naturality
    {U V : C} (f : U ⟶ V) (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v})
    (α : obj.{u, v, w} V ⟶ P) :
    homAddEquiv U P (map f ≫ α) = P.map f.op (homAddEquiv V P α) := by
  exact homEquiv_naturality f P α

/-- The additive universe-raised free-abelian-representable Hom/sections equivalence commutes
with postcomposition in the target presheaf. -/
theorem homAddEquiv_comp
    {U : C} {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}}
    (α : obj.{u, v, w} U ⟶ P) (β : P ⟶ Q) :
    homAddEquiv U Q (α ≫ β) = β.app (op U) (homAddEquiv U P α) := by
  exact homEquiv_comp α β

/-- The inverse additive universe-raised Hom/sections equivalence is natural in the target
presheaf. -/
theorem homAddEquiv_symm_naturality
    (U : C) {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}} (β : P ⟶ Q)
    (s : P.obj (op U)) :
    (homAddEquiv U Q).symm (β.app (op U) s) = (homAddEquiv U P).symm s ≫ β := by
  apply (homAddEquiv U Q).injective
  simp only [homAddEquiv_comp, AddEquiv.apply_symm_apply]

/-- An injective abelian presheaf valued in a raised universe has surjective restriction maps
along monomorphisms in the indexing category. -/
theorem sectionsMap_surjective
    {U V : C} (f : U ⟶ V) [Mono f]
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}) [Injective P] :
    Function.Surjective (P.map f.op) := by
  intro s
  obtain ⟨α, hα⟩ := Injective.factors ((homEquiv U P).symm s) (map.{u, v, w} f)
  refine ⟨homEquiv V P α, ?_⟩
  rw [← homEquiv_naturality, hα, Equiv.apply_symm_apply]

end CategoryTheory.FreeAbelianYoneda.ULift
