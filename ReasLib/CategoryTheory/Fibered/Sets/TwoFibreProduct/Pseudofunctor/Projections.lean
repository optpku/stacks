/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Sets.TwoFibreProduct.Pseudofunctor.Action
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Pseudofunctor.Projections

/-!
# Projection transformations for set-fibred two-fibre products

The neutral projection strong transformations specialize directly to the discrete-fibration
full subbicategory. This retains their generic naturality and coherence data without rebuilding
it at the Sets layer.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory
open scoped Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Sets.TwoFibreProduct

variable {S T : Bicategory.Cospan
  (FiberedCategoryOver.Sets.{u, v, max w (max u (max v vB)), max v vB} C)}

/-- The forward morphism of the equivalence induced by an equivalence of set-fibred cospans is
the direct two-fibre-product map. -/
@[simp]
theorem pseudofunctor.mapEquivalence.hom (e : S ≌ T) :
    ((pseudofunctor C).mapEquivalence e).hom =
      _root_.CategoryTheory.FiberedCategoryOver.Sets.TwoFibreProduct.map e.hom := sorry

/-- The inverse morphism of the equivalence induced by an equivalence of set-fibred cospans is
the direct two-fibre-product map. -/
@[simp]
theorem pseudofunctor.mapEquivalence.inv (e : S ≌ T) :
    ((pseudofunctor C).mapEquivalence e).inv =
      _root_.CategoryTheory.FiberedCategoryOver.Sets.TwoFibreProduct.map e.inv := sorry

/-- The unit of the mapped equivalence is the canonical pseudofunctorial unit. -/
@[simp]
theorem pseudofunctor.mapEquivalence.unit (e : S ≌ T) :
    ((pseudofunctor C).mapEquivalence e).unit =
      Pseudofunctor.mapEquivalence.unitIso (pseudofunctor C) e := sorry

/-- The counit of the mapped equivalence is heterogeneously equal to the canonical
pseudofunctorial counit; the endpoint difference is confined to the full-sub lift. -/
theorem pseudofunctor.mapEquivalence.counit (e : S ≌ T) :
    ((pseudofunctor C).mapEquivalence e).counit ≍
      Pseudofunctor.mapEquivalence.counitIso (pseudofunctor C) e := sorry

variable (C) in
/-- The canonical first projection from the set-fibred two-fibre-product pseudofunctor to the
left endpoint of a bundled cospan. -/
@[stacks 0047 "first projection strong transformation for set-fibred two-fibre-products"]
noncomputable def pseudofunctor.fst :
    Pseudofunctor.StrongTrans (pseudofunctor C)
      (Bicategory.Cospan.leftProjection
        (FiberedCategoryOver.Sets.{u, v, max w (max u (max v vB)), max v vB} C)) :=
  _root_.CategoryTheory.TwoFibreProduct.pseudofunctor.fst
    (BasedCategory.isFiberedInSets C)

variable (C) in
/-- The canonical second projection from the set-fibred two-fibre-product pseudofunctor to the
right endpoint of a bundled cospan. -/
@[stacks 0047 "second projection strong transformation for set-fibred two-fibre-products"]
noncomputable def pseudofunctor.snd :
    Pseudofunctor.StrongTrans (pseudofunctor C)
      (Bicategory.Cospan.rightProjection
        (FiberedCategoryOver.Sets.{u, v, max w (max u (max v vB)), max v vB} C)) :=
  _root_.CategoryTheory.TwoFibreProduct.pseudofunctor.snd
    (BasedCategory.isFiberedInSets C)

/-- The first-projection component is the neutral selected first projection. -/
@[simp]
theorem pseudofunctor.fst.app (S : Bicategory.Cospan
    (FiberedCategoryOver.Sets.{u, v, max w (max u (max v vB)), max v vB} C)) :
    (pseudofunctor.fst C).app S =
      _root_.CategoryTheory.TwoFibreProduct.fst S.fst S.snd := sorry

/-- The naturality isomorphism of the first projection is the neutral selected comparison. -/
@[simp]
theorem pseudofunctor.fst.naturality (psi : S ⟶ T) :
    (pseudofunctor.fst C).naturality psi ≍
      _root_.CategoryTheory.TwoFibreProduct.pseudofunctor.fstIso psi := sorry

/-- The second-projection component is the neutral selected second projection. -/
@[simp]
theorem pseudofunctor.snd.app (S : Bicategory.Cospan
    (FiberedCategoryOver.Sets.{u, v, max w (max u (max v vB)), max v vB} C)) :
    (pseudofunctor.snd C).app S =
      _root_.CategoryTheory.TwoFibreProduct.snd S.fst S.snd := sorry

/-- The naturality isomorphism of the second projection is the neutral selected comparison. -/
@[simp]
theorem pseudofunctor.snd.naturality (psi : S ⟶ T) :
    (pseudofunctor.snd C).naturality psi ≍
      _root_.CategoryTheory.TwoFibreProduct.pseudofunctor.sndIso psi := sorry

end FiberedCategoryOver.Sets.TwoFibreProduct

end CategoryTheory
