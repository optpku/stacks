/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.CostandardSimplex
import StacksCheckRecall

/-!
@stack 017M
-/

@[expose] public section

open CategoryTheory Limits Opposite
open scoped Simplicial SimplexCategory.Truncated

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable (k : ℕ) (X : C)

/- The natural-in-source owner behind part (1) is the Mathlib-style representation of the
universe-lifted evaluation-Hom presheaf by the coyoneda-indexed product. -/
#check Functor.indexedProd.coyoneda.representableBy (C := C) ⦋k⦌ X

/- Lemma 14.15.2 (1): maps from a simplicial object into the indexed product associated to the
costandard `k`-simplex are canonically maps from its value in degree `k` to `X`. -/
@[stacks 017M]
#check (Functor.indexedProd.coyoneda.homEquiv (C := C) ⦋k⦌ X :
  (V : SimplicialObject C) →
    (V ⟶ Functor.indexedProd (coyoneda.obj (op ⦋k⦌))
      ((Functor.const SimplexCategoryᵒᵖ).obj X)) ≃
      (V.obj (op ⦋k⦌) ⟶ X))

/- The equivalence in part (1) evaluates at degree `k` and projects to the identity-indexed
factor. -/
#check (fun {V : SimplicialObject C}
    (γ : V ⟶ Functor.indexedProd (coyoneda.obj (op ⦋k⦌))
      ((Functor.const SimplexCategoryᵒᵖ).obj X)) ↦
  Functor.indexedProd.coyoneda.homEquiv.apply (C := C) ⦋k⦌ (X := X) γ)
#check Functor.indexedProd.coyoneda.homEquiv.symm_apply_π (C := C) ⦋k⦌ (X := X)
#check (fun {V W : SimplicialObject C} (a : W ⟶ V)
    (γ : V ⟶ Functor.indexedProd (coyoneda.obj (op ⦋k⦌))
      ((Functor.const SimplexCategoryᵒᵖ).obj X)) ↦
  Functor.indexedProd.coyoneda.homEquiv.precomp (C := C) ⦋k⦌ (X := X) a γ)
#check (fun {Y : C} {V : SimplicialObject C} (f : X ⟶ Y)
    (γ : V ⟶ Functor.indexedProd (coyoneda.obj (op ⦋k⦌))
      ((Functor.const SimplexCategoryᵒᵖ).obj X)) ↦
  Functor.indexedProd.coyoneda.homEquiv.postcomp (C := C) ⦋k⦌ (X := X) f γ)

/- Lemma 14.15.2 (3): the simplicial object denoted `Hom(C[k], X)` is the indexed product whose
indexing cosimplicial set is the canonical covariant representable at `⦋k⦌`. -/
@[stacks 017M]
#check (Functor.indexedProd (coyoneda.obj (op ⦋k⦌))
  ((Functor.const SimplexCategoryᵒᵖ).obj X) : SimplicialObject C)

/- Restricting the costandard `k`-simplex to the `k`-truncated simplex category is represented
by its top object there. -/
#check (CosimplicialObject.Truncated.coyoneda.iso ⦋k, le_rfl⦌ₖ :
  (CosimplicialObject.truncation k).obj
      (coyoneda.obj (op ⦋k⦌) : CosimplicialObject (Type)) ≅
    (coyoneda.obj (op ⦋k, le_rfl⦌ₖ) : CosimplicialObject.Truncated (Type) k))
#check CosimplicialObject.Truncated.coyoneda.iso_app
#check Functor.indexedProd.coyoneda.iso.inv_app_π
#check SimplicialObject.Truncated.coyoneda.iso_app
#check SimplicialObject.Truncated.coyoneda.iso.inv_app_π

/- The natural-in-source owner behind part (2) transports the generic representation along
the truncation comparison and removes the unnecessary universe lift. -/
@[stacks 017M]
#check (SimplicialObject.Truncated.coyoneda.representableBy
    (C := C) ⦋k, le_rfl⦌ₖ X :
  (((evaluation (SimplexCategory.Truncated k)ᵒᵖ C).obj
      (op ⦋k, le_rfl⦌ₖ)).op ⋙ yoneda.obj X).RepresentableBy
    ((SimplicialObject.truncation k).obj
      (Functor.indexedProd (coyoneda.obj (op ⦋k⦌))
        ((Functor.const SimplexCategoryᵒᵖ).obj X))))

/- Lemma 14.15.2 (2): the analogous equivalence for a `k`-truncated simplicial object uses the
top truncated simplex `⦋k, le_rfl⦌ₖ`. -/
@[stacks 017M]
#check (SimplicialObject.Truncated.coyoneda.homEquiv
    (C := C) ⦋k, le_rfl⦌ₖ X :
  (W : SimplicialObject.Truncated C k) →
    (W ⟶ (SimplicialObject.truncation k).obj
      (Functor.indexedProd (coyoneda.obj (op ⦋k⦌))
        ((Functor.const SimplexCategoryᵒᵖ).obj X))) ≃
      (W.obj (op ⦋k, le_rfl⦌ₖ) ⟶ X))

/- The truncated equivalence evaluates at the top degree and projects to the factor indexed by
the identity of `⦋k⦌`. -/
#check (fun {W : SimplicialObject.Truncated C k}
    (γ : W ⟶ (SimplicialObject.truncation k).obj
      (Functor.indexedProd (coyoneda.obj (op ⦋k⦌))
        ((Functor.const SimplexCategoryᵒᵖ).obj X))) ↦
  SimplicialObject.Truncated.coyoneda.homEquiv.apply
    (C := C) (k := k) (d := ⦋k, le_rfl⦌ₖ) (X := X) γ)

end CategoryTheory
