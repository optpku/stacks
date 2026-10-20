/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Predeformation
import StacksCheckRecall

/-!
# Formal objects in the residue-point predeformation category

A formal object over a locally Noetherian scheme determines a formal object of
its residue-point predeformation category with the same base and stages.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

/- Remark 98.9.2: a formal object of a category fibred in groupoids over `S`
defines a formal object of the predeformation category at its residue object.
Stage `n` below is the source stage `ξ_{n+1}`, and stage zero is `x₀ = ξ₁`. -/
@[stacks 0CXH] #check
  (AlgebraicGeometry.GroupoidsOver.Predeformation.formalObjectOfAdicSystem :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
      {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
      (toS : Spec (CommRingCat.of R) ⟶ S)
      (objects : ℕ → X.total) (step : ∀ n, objects n ⟶ objects (n + 1))
      (over_obj : ∀ n, X.p.obj (objects n) =
        AdicPresentation.stage toS (maximalIdeal R) n)
      (over_step : ∀ n, X.p.IsHomLift
        ((AdicPresentation.diagram toS (maximalIdeal R)).map (homOfLE (Nat.le_succ n)))
        (step n))
      {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
      [Algebra Λ R] [Module.Finite Λ (ResidueField R)]
      (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
      (h_toS : Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ openImmersion = toS)
      [LocallyOfFiniteType (GroupoidsOver.Predeformation.adicResidueToS toS)],
      _root_.FormalObject
        (GroupoidsOver.Predeformation.adicProjection toS objects over_obj openImmersion h_toS))
