/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor.Fiberwise
public import ReasLib.CategoryTheory.Sites.Descent.IndexedFunctor.DescentData.Basic

import Mathlib.Tactic.CrossRefAttribute

/-!
# Fiberwise properties of descent-data transport

This leaf upgrades identity-base transport of descent data with fullness, faithfulness, hom-set
equivalences, and equivalence-of-categories results inherited from the fiber functors.
-/

@[expose] public section

universe t uC vC uF vF uG vG

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

namespace Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

variable {C : Type uC} [Category.{vC} C]
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}}
variable {G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vG, uG}}
variable (H : IndexedFunctor (𝟭 C) F G)
variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- A fiberwise-fully-faithful indexed functor induces a full functor on every descent-data
category. -/
@[stacks 026F "fiberwise-full descent-data transport"]
instance mapDescentData.full [H.FiberwiseFullyFaithful] :
    (H.mapDescentData f).Full := sorry

/-- A fiberwise-fully-faithful indexed functor induces a faithful functor on every
descent-data category. -/
@[stacks 026F "fiberwise-faithful descent-data transport"]
instance mapDescentData.faithful [H.FiberwiseFullyFaithful] :
    (H.mapDescentData f).Faithful := sorry

/-- For a fiberwise-fully-faithful indexed functor, componentwise transport is an equivalence
between morphisms of descent data. -/
@[stacks 026F "fiberwise-fully-faithful descent hom equivalence"]
noncomputable def mapDescentData.homEquiv [H.FiberwiseFullyFaithful]
    (D₁ D₂ : F.DescentData f) :
    (D₁ ⟶ D₂) ≃
      ((H.mapDescentData f).obj D₁ ⟶ (H.mapDescentData f).obj D₂) :=
  (Functor.FullyFaithful.ofFullyFaithful (H.mapDescentData f)).homEquiv

/-- The descent-data hom equivalence obtained from an explicit fiberwise-full-faithfulness
proof. This avoids requiring clients whose hypothesis is ordinary theorem data to install a
temporary `FiberwiseFullyFaithful` instance. -/
@[stacks 026F "explicit-proof fiberwise descent hom equivalence"]
noncomputable def mapDescentData.homEquivOf
    (hH : H.FiberwiseFullyFaithful)
    (D₁ D₂ : F.DescentData f) :
    (D₁ ⟶ D₂) ≃
      ((H.mapDescentData f).obj D₁ ⟶ (H.mapDescentData f).obj D₂) :=
  -- Local instance justification (proof-local temporary data): the underlying generic
  -- `mapDescentData.homEquiv` is deliberately typeclass-driven so that its full and faithful
  -- component instances are available internally; this explicit-proof bridge keeps that
  -- registration out of every downstream client.
  letI : H.FiberwiseFullyFaithful := hH
  mapDescentData.homEquiv H f D₁ D₂

/-- The explicit-proof descent-data hom equivalence maps a morphism by the ordinary
descent-data transport functor. -/
@[simp, stacks 026F "explicit-proof descent hom equivalence application"]
theorem mapDescentData.HomEquivOf.apply
    (hH : H.FiberwiseFullyFaithful)
    (D₁ D₂ : F.DescentData f) (φ : D₁ ⟶ D₂) :
    mapDescentData.homEquivOf H f hH D₁ D₂ φ =
      (H.mapDescentData f).map φ := sorry

/-- The forward descent-data hom equivalence is the morphism action of
`mapDescentData`. -/
@[simp, stacks 026F "descent hom equivalence application"]
theorem mapDescentData.HomEquiv.apply [H.FiberwiseFullyFaithful]
    (D₁ D₂ : F.DescentData f) (φ : D₁ ⟶ D₂) :
    mapDescentData.homEquiv H f D₁ D₂ φ =
      (H.mapDescentData f).map φ := sorry

/-- Components of inverse descent-data hom transport are inverse component hom transports. -/
@[simp, stacks 026F "descent hom equivalence inverse component"]
theorem mapDescentData.HomEquiv.symm_apply_hom
    [H.FiberwiseFullyFaithful]
    (D₁ D₂ : F.DescentData f)
    (ψ : (H.mapDescentData f).obj D₁ ⟶
      (H.mapDescentData f).obj D₂) (i : ι) :
    ((mapDescentData.homEquiv H f D₁ D₂).symm ψ).hom i =
      ((Functor.FullyFaithful.ofFullyFaithful
        (H.app (X i))).homEquiv).symm (ψ.hom i) := sorry

/-- Inverse descent-data hom transport preserves identity morphisms. -/
@[simp, stacks 026F "descent hom equivalence inverse identity"]
theorem mapDescentData.HomEquiv.symm_apply_id
    [H.FiberwiseFullyFaithful] (D : F.DescentData f) :
    (mapDescentData.homEquiv H f D D).symm
        (𝟙 ((H.mapDescentData f).obj D)) =
      𝟙 D := sorry

/-- Inverse descent-data hom transport preserves composition. -/
@[stacks 026F "descent hom equivalence inverse composition"]
theorem mapDescentData.HomEquiv.symm_apply_comp
    [H.FiberwiseFullyFaithful]
    (D₁ D₂ D₃ : F.DescentData f)
    (φ : (H.mapDescentData f).obj D₁ ⟶
      (H.mapDescentData f).obj D₂)
    (ψ : (H.mapDescentData f).obj D₂ ⟶
      (H.mapDescentData f).obj D₃) :
    (mapDescentData.homEquiv H f D₁ D₃).symm (φ ≫ ψ) =
      (mapDescentData.homEquiv H f D₁ D₂).symm φ ≫
        (mapDescentData.homEquiv H f D₂ D₃).symm ψ := sorry

/-- A fiberwise equivalence induces an equivalence on every category of descent data over the
same base family. -/
@[stacks 026F "fiberwise-equivalence descent-data transport"]
instance mapDescentData.isEquivalence [H.FiberwiseEquivalence] :
    (H.mapDescentData f).IsEquivalence := sorry

end Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

end CategoryTheory
