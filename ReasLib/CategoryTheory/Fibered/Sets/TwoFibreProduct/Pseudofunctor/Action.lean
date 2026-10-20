/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.InSets.Hom
public import ReasLib.CategoryTheory.Fibered.Sets.TwoFibreProduct.Pseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Pseudofunctor.Computations

/-!
# Action of two-fibre products of categories fibred in sets

This leaf owns direct `1`-cell, `2`-cell, and local Hom actions. Their data are the explicit
based pseudo-pullback actions, lifted only through the locally full induced bicategory.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open BasedCategory Bicategory
open scoped Bicategory
open scoped Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Sets.TwoFibreProduct

variable {S T : Bicategory.Cospan
  (FiberedCategoryOver.Sets.{u, v, max w (max u (max v vB)), max v vB} C)}

/-- The direct map of set-fibred two-fibre products induced by a bundled cospan morphism. -/
@[stacks 0047 "map of bundled cospans of categories fibred in sets"]
noncomputable def map (psi : S ⟶ T) :
    (pseudofunctor C).obj S ⟶ (pseudofunctor C).obj T :=
  Bicategory.InducedBicategory.mkHom
    (BasedCategory.PseudoPullback.map
      (_root_.CategoryTheory.TwoFibreProduct.CospanTransform.forget
        (Bicategory.Cospan.Hom.toCospanTransform psi)))

/-- The direct action on a `2`-morphism of bundled set-fibred cospans. -/
@[stacks 0047 "2-morphism action on bundled cospans of categories fibred in sets"]
noncomputable def map₂ {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :
    map psi ⟶ map phi :=
  Bicategory.InducedBicategory.mkHom₂
    (BasedCategory.PseudoPullback.map₂
      (_root_.CategoryTheory.TwoFibreProduct.CospanModification.forget
        (Bicategory.Cospan.Hom₂.toModification Gamma)))

/-- The direct action on cospan `2`-cells preserves identities. -/
@[simp]
theorem map₂.id (psi : S ⟶ T) :
    map₂ (𝟙 psi) = 𝟙 (map psi) := sorry

/-- The direct action on cospan `2`-cells preserves vertical composition. -/
@[simp]
theorem map₂.comp {psi phi chi : S ⟶ T}
    (Gamma : psi ⟶ phi) (Delta : phi ⟶ chi) :
    map₂ (Gamma ≫ Delta) = map₂ Gamma ≫ map₂ Delta := sorry

/-- The direct local Hom functor of two-fibre products of categories fibred in sets. -/
@[stacks 0047 "local Hom functor for bundled cospans of categories fibred in sets"]
noncomputable def mapFunctor (S T : Bicategory.Cospan
    (FiberedCategoryOver.Sets.{u, v, max w (max u (max v vB)), max v vB} C)) :
    (S ⟶ T) ⥤ ((pseudofunctor C).obj S ⟶ (pseudofunctor C).obj T) :=
  { obj := map
    map := map₂
    map_id := map₂.id
    map_comp := map₂.comp }

/-- The object action is the neutral explicit two-fibre-product apex selected by the
discrete-fibration property. -/
@[simp]
theorem pseudofunctor.obj (S : Bicategory.Cospan
    (FiberedCategoryOver.Sets.{u, v, max w (max u (max v vB)), max v vB} C)) :
    (pseudofunctor C).obj S =
      _root_.CategoryTheory.TwoFibreProduct.apex S.fst S.snd := sorry

/-- Forgetting the set-fibred owner from the direct map recovers the explicit based
pseudo-pullback map. -/
@[simp]
theorem map.hom (psi : S ⟶ T) :
    (map psi).hom =
      BasedCategory.PseudoPullback.map
        (_root_.CategoryTheory.TwoFibreProduct.CospanTransform.forget
          (Bicategory.Cospan.Hom.toCospanTransform psi)) := sorry

/-- The based functor underlying the direct map is the explicit based pseudo-pullback map. -/
@[simp]
theorem map.toBasedFunctor (psi : S ⟶ T) :
    FiberedCategoryOver.Sets.toBasedFunctor (map psi) =
      BasedCategory.PseudoPullback.map
        (_root_.CategoryTheory.TwoFibreProduct.CospanTransform.forget
          (Bicategory.Cospan.Hom.toCospanTransform psi)) := sorry

/-- The total functor underlying the direct map is the total functor of the explicit based
pseudo-pullback map. -/
@[simp]
theorem map.toFunctor (psi : S ⟶ T) :
    FiberedCategoryOver.Sets.toFunctor (map psi) =
      (BasedCategory.PseudoPullback.map
        (_root_.CategoryTheory.TwoFibreProduct.CospanTransform.forget
          (Bicategory.Cospan.Hom.toCospanTransform psi))).toFunctor := sorry

/-- Forgetting the set-fibred owner from the direct `2`-cell recovers the explicit based
pseudo-pullback action. -/
theorem map₂.hom {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :
    (map₂ Gamma).hom ≍
      BasedCategory.PseudoPullback.map₂
        (_root_.CategoryTheory.TwoFibreProduct.CospanModification.forget
          (Bicategory.Cospan.Hom₂.toModification Gamma)) := sorry

/-- The pseudofunctor `1`-cell field is the direct public set-fibred map. -/
@[simp]
theorem pseudofunctor.map (psi : S ⟶ T) :
    (pseudofunctor C).map psi = map psi := sorry

/-- The pseudofunctor `2`-cell field is the direct public set-fibred action. -/
theorem pseudofunctor.map₂ {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :
    (pseudofunctor C).map₂ Gamma ≍ map₂ Gamma := sorry

/-- The pseudofunctor local action is the direct public Hom functor. -/
@[simp]
theorem pseudofunctor.mapFunctor (S T : Bicategory.Cospan
    (FiberedCategoryOver.Sets.{u, v, max w (max u (max v vB)), max v vB} C)) :
    (pseudofunctor C).mapFunctor S T = mapFunctor S T := sorry

/-- The object action of the direct local Hom functor is `map`. -/
@[simp]
theorem mapFunctor.obj (psi : S ⟶ T) :
    (mapFunctor S T).obj psi = map psi := sorry

/-- The morphism action of the direct local Hom functor is `map₂`. -/
theorem mapFunctor.map {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :
    (mapFunctor S T).map Gamma ≍ map₂ Gamma := sorry

end FiberedCategoryOver.Sets.TwoFibreProduct

end CategoryTheory
