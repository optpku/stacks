module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.LargeColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import ReasLib.CategoryTheory.Functor.FreeAbelianYoneda
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Free-abelian Čech cover complexes

This module owns the Čech simplicial formal coproduct built from the iterated fibre products of a
fixed-target family.  It keeps the product hypothesis local to that family, then applies the
free-abelian Yoneda functor to obtain the chain complex used to resolve a Čech cover.
-/

@[expose] public section

noncomputable section

universe w u v

namespace CategoryTheory

open Limits Opposite AlgebraicTopology

/-- A fixed-target family has all finite iterated fibre products needed for its Čech nerve. -/
@[stacks 03AS "iterated fibre products for a fixed-target family"]
class HasIteratedFiberProducts {C : Type u} [Category.{v} C] {U : C} {ι : Type w}
    (family : ι → Over U) : Prop where
  hasProduct : ∀ p : ℕ, ∀ f : Fin (p + 1) → ι, HasProduct (family ∘ f)

/-- Finite products in the slice provide the iterated fibre products of every fixed-target family.
-/
@[stacks 03AS "finite-product instance for iterated fibre products"]
instance hasIteratedFiberProducts_of_hasFiniteProducts {C : Type u} [Category.{v} C] {U : C}
    {ι : Type w} (family : ι → Over U) [HasFiniteProducts (Over U)] :
    HasIteratedFiberProducts family where
  hasProduct := fun _ _ => inferInstance

/-- The selected product of a tuple in a family with iterated fibre products. -/
@[stacks 03AS "selected family product"]
abbrev familyHasProduct {C : Type u} [Category.{v} C] {U : C} {ι : Type w}
    (family : ι → Over U) [HasIteratedFiberProducts family] (p : ℕ)
    (f : Fin (p + 1) → ι) : HasProduct (family ∘ f) :=
  HasIteratedFiberProducts.hasProduct p f

/-- The degree-`p` formal coproduct of iterated fibre products of a fixed-target family. -/
@[stacks 03AS "degreewise family power"]
noncomputable def familyPower {C : Type u} [Category.{v} C] {U : C} {ι : Type w}
    (family : ι → Over U) [HasIteratedFiberProducts family] (p : ℕ) :
    FormalCoproduct.{w} (Over U) where
  I := Fin (p + 1) → ι
  obj f :=
    -- Pin the selected family product; an ambient finite-product instance may be a different
    -- non-definitional choice.
    -- Local instance justification (defeq pin): selected source product for `familyPower`.
    letI := familyHasProduct family p f
    ∏ᶜ (family ∘ f)

/-- The projection from a degree-`p` family power to its `a`-th member of the original family. -/
@[stacks 03AS "family power projection"]
noncomputable def familyPowerProjection {C : Type u} [Category.{v} C] {U : C} {ι : Type w}
    (family : ι → Over U) [HasIteratedFiberProducts family] (p : ℕ) (a : Fin (p + 1)) :
    familyPower family p ⟶ FormalCoproduct.mk ι family where
  f i := i a
  φ i :=
    -- Reuse the product witness selected by `familyPower`; changing it here would change the
    -- source object definitionally and would no longer describe its canonical projection.
    -- Local instance justification (defeq pin): selected source product for the projection.
    letI := familyHasProduct family p i
    Pi.π (family ∘ i) a

/-- Reindex an iterated-fibre-product formal coproduct along a map of finite index tuples. -/
@[stacks 03AS "family power reindexing"]
noncomputable def familyMapPower {C : Type u} [Category.{v} C] {U : C} {ι : Type w}
    (family : ι → Over U) [HasIteratedFiberProducts family] {p q : ℕ}
    (g : Fin (p + 1) → Fin (q + 1)) :
    familyPower family q ⟶ familyPower family p where
  f i := i ∘ g
  φ i :=
    -- Both witnesses must agree with the source and target objects selected by `familyPower`.
    -- Local instance justification (defeq pin): selected source product for the reindexing map.
    letI := familyHasProduct family q i
    -- Local instance justification (defeq pin): selected target product for the reindexing map.
    letI := familyHasProduct family p (i ∘ g)
    Pi.lift (fun a ↦ Pi.π (family ∘ i) (g a))

/-- Reindexing an iterated-fibre-product formal coproduct along an identity map is the identity.
-/
theorem familyMapPower_id {C : Type u} [Category.{v} C] {U : C} {ι : Type w}
    (family : ι → Over U) [HasIteratedFiberProducts family] (p : ℕ) :
    familyMapPower family (id : Fin (p + 1) → Fin (p + 1)) = 𝟙 (familyPower family p) := sorry

/-- Reindexing an iterated-fibre-product formal coproduct reverses composition of index maps. -/
theorem familyMapPower_comp {C : Type u} [Category.{v} C] {U : C} {ι : Type w}
    (family : ι → Over U) [HasIteratedFiberProducts family] {p q r : ℕ}
    (first : Fin (p + 1) → Fin (q + 1)) (second : Fin (q + 1) → Fin (r + 1)) :
    familyMapPower family (second ∘ first) =
      familyMapPower family second ≫ familyMapPower family first := sorry

/-- The Čech simplicial formal coproduct of a fixed-target family, constructed from its iterated
fibre products. -/
@[stacks 03AS "family Cech simplicial object"]
noncomputable def familyCech {C : Type u} [Category.{v} C] {U : C} {ι : Type w}
    (family : ι → Over U) [HasIteratedFiberProducts family] :
    SimplicialObject (FormalCoproduct.{w} (Over U)) where
  obj n := familyPower family n.unop.len
  map f := familyMapPower family f.unop.toOrderHom
  map_id := fun n => familyMapPower_id family n.unop.len
  map_comp := fun f g => familyMapPower_comp family g.unop.toOrderHom f.unop.toOrderHom

/-- The degree of `familyCech` is the corresponding formal coproduct of iterated fibre products.
-/
@[simp]
theorem familyCech_obj {C : Type u} [Category.{v} C] {U : C} {ι : Type w}
    (family : ι → Over U) [HasIteratedFiberProducts family] (n : SimplexCategoryᵒᵖ) :
    (familyCech family).obj n = familyPower family n.unop.len := sorry

/-- The `j`-th face of `familyCech` is the reindexing morphism induced by the standard simplex
face injection. -/
@[simp]
theorem familyCech_face {C : Type u} [Category.{v} C] {U : C} {ι : Type w}
    (family : ι → Over U) [HasIteratedFiberProducts family] (n : ℕ) (j : Fin (n + 2)) :
    SimplicialObject.δ (familyCech family) j =
      familyMapPower family (SimplexCategory.δ j).toOrderHom := sorry

/-- The chain complex of additive presheaves obtained from the free-abelian Čech simplicial
formal coproduct of a fixed-target family. -/
/- This is the slice-valued presentation used by the sectionwise companion below. -/
abbrev freeAbelianCechChainComplex {C : Type u} [Category.{v} C] {U : C}
    [HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{v})] [HasProducts AddCommGrpCat.{v}]
    {ι : Type w} (family : ι → Over U) [HasIteratedFiberProducts family] :
    ChainComplex ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{v}) ℕ :=
  (alternatingFaceMapComplex ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{v})).obj
    (familyCech family ⋙
      (FormalCoproduct.eval.{w} (Over U) ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{v})).obj
        FreeAbelianYoneda.functor)

/-- The free-abelian Čech chain complex on the slice has zero homology in degree `i + 1`. -/
theorem freeAbelianCechCoverChainComplex_homology_isZero_succ
    {C : Type u} [Category.{v} C] {U : C} {ι : Type w} (family : ι → Over U)
    [HasIteratedFiberProducts family] [HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{v})]
    [HasProducts AddCommGrpCat.{v}] (i : ℕ) :
    IsZero ((freeAbelianCechChainComplex family).homology (i + 1)) := sorry

/-- The free-abelian Čech chain complex on the slice has zero homology in every positive degree. -/
theorem freeAbelianCechCoverChainComplex_homology_isZero_of_pos {C : Type u} [Category.{v} C]
    {U : C} {ι : Type w} (family : ι → Over U) [HasIteratedFiberProducts family]
    [HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{v})] [HasProducts AddCommGrpCat.{v}]
    (i : ℕ) (hi : 0 < i) :
    IsZero ((freeAbelianCechChainComplex family).homology i) := sorry

end CategoryTheory
