/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap61.Lemma_61_19_5_Adjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.19.5

The derived adjunction unit of `ε⁻¹ ⊣ Rε_*` is an isomorphism on `D⁺(X.Etale)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})
variable [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (etaleToProEt X).op.HasLeftKanExtension F]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1}]
variable [PreservesFiniteLimits (etaleToProEtPullback X AddCommGrpCat.{u + 1})]
variable [PreservesFiniteColimits (etaleToProEtPullback X AddCommGrpCat.{u + 1})]

/-- Lemma 61.19.5 (1): for a scheme `X` and an abelian sheaf `F` on `X.Etale`,
`Rε_* (ε⁻¹ F) = F`. Equivalently, the canonical derived unit
`etaleToProEt_derivedUnit` at `F[0]` is an isomorphism. -/
@[stacks 099V]
theorem etaleToProEt_plusAdjunction_unit_app_single_isIso
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso
      (etaleToProEt_derivedUnit X
        ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (0 : ℤ)).obj F)) :=
  sorry

/-- Lemma 61.19.5 (2): for a scheme `X` and `K` in `D⁺(X.Etale)`, the map
`K ⟶ Rε_* ε⁻¹ K` given by `etaleToProEt_derivedUnit` is an isomorphism. -/
@[stacks 099V]
theorem etaleToProEt_plusAdjunction_unit_app_isIso
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    IsIso (etaleToProEt_derivedUnit X K) :=
  sorry

end AlgebraicGeometry.Scheme

end

end
