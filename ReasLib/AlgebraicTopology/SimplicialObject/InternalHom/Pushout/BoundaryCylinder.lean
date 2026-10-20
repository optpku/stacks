/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Variance
public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Pushout.IsPullback
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# Internal hom of a standard-simplex boundary cylinder

This leaf specializes the generic internal-hom pushout theorem to the boundary-cylinder pushout.
Keeping the specialization separate prevents the generic pushout owner from importing the
simplicial-set boundary and monoidal APIs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped MonoidalCategory Simplicial

noncomputable section

universe vC uC uS

namespace CategoryTheory.SimplicialObject.internalHom.boundaryCylinder

variable {C : Type uC} [Category.{vC} C] (k : ℕ) (T : SimplicialObject C)

variable
  [HasCopowers ((∂Δ[k] : SSet.{uS}) ⊗ (∂Δ[1] : SSet.{uS})) C]
  [HasCopowers ((Δ[k] : SSet.{uS}) ⊗ (∂Δ[1] : SSet.{uS})) C]
  [HasCopowers ((∂Δ[k] : SSet.{uS}) ⊗ (Δ[1] : SSet.{uS})) C]
  [HasCopowers
    ((∂Δ[k] : (Δ[k] : SSet.{uS}).Subcomplex).unionProd
      (∂Δ[1] : (Δ[1] : SSet.{uS}).Subcomplex) : SSet.{uS}) C]
  [HasInternalHom ((∂Δ[k] : SSet.{uS}) ⊗ (∂Δ[1] : SSet.{uS})) T]
  [HasInternalHom ((Δ[k] : SSet.{uS}) ⊗ (∂Δ[1] : SSet.{uS})) T]
  [HasInternalHom ((∂Δ[k] : SSet.{uS}) ⊗ (Δ[1] : SSet.{uS})) T]
  [HasInternalHom
    ((∂Δ[k] : (Δ[k] : SSet.{uS}).Subcomplex).unionProd
      (∂Δ[1] : (Δ[1] : SSet.{uS}).Subcomplex) : SSet.{uS}) T]

/-- Lemma 25.9.1 (01GP): precomposition turns the canonical pushout presenting the
boundary of the standard-simplex cylinder into a pullback of internal mapping objects.
The textbook statement is the specialization `k = n + 1`; its two factors are the endpoint
copies `Δ[k] ⊗ ∂Δ[1]` and the boundary cylinder `∂Δ[k] ⊗ Δ[1]`. Cartesian symmetry
exchanges this canonical `unionProd` order with the source's order `Δ[1] ⊗ Δ[k]`. -/
@[stacks 01GP "internal hom of the standard-simplex boundary cylinder"]
theorem isPullback :
    IsPullback
      (precomp
        (SSet.Subcomplex.unionProd.ι₁
          (∂Δ[k] : (Δ[k] : SSet.{uS}).Subcomplex)
          (∂Δ[1] : (Δ[1] : SSet.{uS}).Subcomplex)) T)
      (precomp
        (SSet.Subcomplex.unionProd.ι₂
          (∂Δ[k] : (Δ[k] : SSet.{uS}).Subcomplex)
          (∂Δ[1] : (Δ[1] : SSet.{uS}).Subcomplex)) T)
      (precomp
        ((∂Δ[k] : (Δ[k] : SSet.{uS}).Subcomplex).ι ▷ (∂Δ[1] : SSet.{uS})) T)
      (precomp
        ((∂Δ[k] : SSet.{uS}) ◁
          (∂Δ[1] : (Δ[1] : SSet.{uS}).Subcomplex).ι) T) := sorry

end CategoryTheory.SimplicialObject.internalHom.boundaryCylinder
