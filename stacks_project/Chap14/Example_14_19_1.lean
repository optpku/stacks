/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Zero.Comparison
import StacksCheckRecall

/-!
@stack 0182

# Example 14.19.1 compatibility facade

ReasLib owns the object-specific finite-self-product model of `cosk₀`, its universal property,
its canonical comparison with right Kan extension, and the bridge to Mathlib's terminal Cech
nerve.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject.ZeroCoskeleton

variable {C : Type u} [Category.{v} C]

section SelfProducts

variable (X : C) [HasPositivePowers X]
variable (V : SimplicialObject C)

/- Example 14.19.1 (1): degree `n` of the explicit zero coskeleton is `X^(n + 1)`. -/
@[stacks 0182 "Example 14.19.1 (1)"]
#check (selfProduct.obj X :
  ∀ Delta : SimplexCategoryᵒᵖ,
    (selfProduct X).obj Delta =
      ∏ᶜ (fun _ : Fin (Delta.unop.len + 1) ↦ X))

/- The explicit model is functorial, and simplex operators reindex its product projections. -/
#check (selfProduct.map.π X :
  ∀ {Delta Delta' : SimplexCategoryᵒᵖ} (theta : Delta ⟶ Delta')
      (i : Fin (Delta'.unop.len + 1)),
    (selfProduct X).map theta ≫
        Pi.π (fun _ : Fin (Delta'.unop.len + 1) ↦ X) i =
      Pi.π (fun _ : Fin (Delta.unop.len + 1) ↦ X)
        (theta.unop.toOrderHom i))

/- The universal property can also be read componentwise through the product projections. -/
#check (homEquiv.app_π X :
  ∀ {V : SimplicialObject C} (f : V ⟶ selfProduct X)
      (Delta : SimplexCategoryᵒᵖ) (i : Fin (Delta.unop.len + 1)),
    f.app Delta ≫ Pi.π (fun _ : Fin (Delta.unop.len + 1) ↦ X) i =
      V.map (SimplexCategory.const ⦋0⦌ Delta.unop i).op ≫ homEquiv X V f)

/- Example 14.19.1 (2): the explicit model represents maps out of degree zero. -/
@[stacks 0182 "Example 14.19.1 (2)"]
#check (homEquiv X V : (V ⟶ selfProduct X) ≃ (V _⦋0⦌ ⟶ X))

/- The natural-in-source owner of the same universal property needs positive powers only for
the fixed target `X`. -/
@[stacks 0182 "Example 14.19.1: representability companion"]
#check (representableBy X :
  ((evalZero (C := C)).op ⋙ yoneda.obj X).RepresentableBy (selfProduct X))

section ChosenCanonical

variable [((SimplicialObject.Truncated.constZero (C := C)).obj X).HasCoskeleton]

/- The canonical right-Kan-extension classifier and comparison require only the chosen
coskeleton attached to this single coefficient object. -/
#check (canonical.homEquiv X V :
  (V ⟶ ((SimplicialObject.Truncated.constZero (C := C)).obj X).coskeleton) ≃
    (V _⦋0⦌ ⟶ X))
#check canonical.homEquiv.apply X V
#check canonical.homEquiv.symm_apply X V
#check canonical.representableBy X
#check selfProduct.coskIso X
#check selfProduct.coskIso.hom_apply X
#check selfProduct.coskIso.inv_apply X

end ChosenCanonical

end SelfProducts

section CanonicalCoskeleton

variable [∀ X : C, HasPositivePowers X]
variable [SimplicialObject.Truncated.HasCoskeletons C 0]

/- Example 14.19.1, canonical companion: the explicit self-product construction is naturally
isomorphic to the zero-coskeleton obtained by right Kan extension from the constant
zero-truncated simplicial object. -/
@[stacks 0182 "Example 14.19.1: canonical zero-coskeleton companion"]
#check (selfProduct.functorIso (C := C) :
  selfProduct.functor (C := C) ≅
    SimplicialObject.Truncated.constZero (C := C) ⋙
      SimplicialObject.Truncated.cosk (C := C) 0)
#check selfProduct.functorIso_app (C := C)

end CanonicalCoskeleton

section FiniteProducts

variable [HasFiniteProducts C] (X : C)

#check (cechNerve.terminalIso X : selfProduct X ≅ cechNerveTerminalFrom X)
#check cechNerve.terminalIso_app X

end FiniteProducts

end CategoryTheory.SimplicialObject.ZeroCoskeleton
