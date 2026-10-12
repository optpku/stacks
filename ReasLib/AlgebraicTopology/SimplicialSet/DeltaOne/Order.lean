/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.DeltaOne.Endpoint
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Lattice operations on the simplicial interval

The standard one-simplex is degreewise the ordered interval `Fin 2`. Pointwise maximum and
minimum therefore define canonical simplicial maps `Δ[1] ⊗ Δ[1] ⟶ Δ[1]`.
This module owns those maps and their calculation rules independently of any particular
copower or cylinder construction.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite
open SSet.stdSimplex (asOrderHom objMk)
open scoped Simplicial

noncomputable section

universe u

namespace SSet

namespace deltaOne

namespace max

/-- Pointwise maximum of two simplices of `Δ[1]` is monotone. -/
@[stacks 019O "pointwise maximum on interval simplices is monotone"]
theorem monotone (m : SimplexCategoryᵒᵖ)
    (z : ((Δ[1] : SSet.{u}) ⊗ Δ[1]).obj m) :
    Monotone (fun k => max (asOrderHom z.1 k) (asOrderHom z.2 k)) := sorry

/-- The degreewise pointwise-maximum operation on simplices of `Δ[1]`. -/
@[stacks 019O "degreewise pointwise maximum on the simplicial interval"]
def app (m : SimplexCategoryᵒᵖ) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[1]).obj m ⟶ (Δ[1] : SSet.{u}).obj m :=
  ↾fun z =>
    objMk
      { toFun := fun k => max (asOrderHom z.1 k) (asOrderHom z.2 k)
        monotone' := SSet.deltaOne.max.monotone m z }

namespace app

/-- Pointwise maximum commutes with simplicial reindexing. -/
@[stacks 019O "naturality of pointwise maximum on the simplicial interval"]
theorem naturality {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[1]).map f ≫ SSet.deltaOne.max.app n =
      SSet.deltaOne.max.app m ≫ (Δ[1] : SSet.{u}).map f := sorry

end app

/-- Lemma 14.26.8: pointwise maximum as a simplicial map
`Δ[1] ⊗ Δ[1] ⟶ Δ[1]`. -/
@[stacks 019O "pointwise maximum on the simplicial interval"]
noncomputable def map :
    ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⟶ (Δ[1] : SSet.{u}) where
  app := SSet.deltaOne.max.app
  naturality := fun {_ _} f => SSet.deltaOne.max.app.naturality f

namespace map

/-- Evaluation of the pointwise-maximum simplicial map. -/
@[simp, stacks 019O "pointwise-maximum simplicial map formula"]
theorem app_apply (m : SimplexCategoryᵒᵖ)
    (z : ((Δ[1] : SSet.{u}) ⊗ Δ[1]).obj m)
    (k : Fin (m.unop.len + 1)) :
    asOrderHom (SSet.deltaOne.max.map.app m z) k =
      max (asOrderHom z.1 k) (asOrderHom z.2 k) := sorry

/-- At time zero, pointwise maximum is the identity of `Δ[1]`. -/
@[reassoc, stacks 019O "pointwise maximum at the zero endpoint"]
theorem ι₀_comp :
    ι₀ ≫ SSet.deltaOne.max.map = 𝟙 (Δ[1] : SSet.{u}) := sorry

/-- At time one, pointwise maximum is the constant-one endomorphism of `Δ[1]`. -/
@[reassoc, stacks 019O "pointwise maximum at the one endpoint"]
theorem ι₁_comp :
    ι₁ ≫ SSet.deltaOne.max.map = SSet.deltaOne.const (1 : Fin 2) := sorry

end map

end max

namespace min

/-- Pointwise minimum of two simplices of `Δ[1]` is monotone. -/
@[stacks 019O "pointwise minimum on interval simplices is monotone"]
theorem monotone (m : SimplexCategoryᵒᵖ)
    (z : ((Δ[1] : SSet.{u}) ⊗ Δ[1]).obj m) :
    Monotone (fun k => min (asOrderHom z.1 k) (asOrderHom z.2 k)) := sorry

/-- The degreewise pointwise-minimum operation on simplices of `Δ[1]`. -/
@[stacks 019O "degreewise pointwise minimum on the simplicial interval"]
def app (m : SimplexCategoryᵒᵖ) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[1]).obj m ⟶ (Δ[1] : SSet.{u}).obj m :=
  ↾fun z =>
    objMk
      { toFun := fun k => min (asOrderHom z.1 k) (asOrderHom z.2 k)
        monotone' := SSet.deltaOne.min.monotone m z }

namespace app

/-- Pointwise minimum commutes with simplicial reindexing. -/
@[stacks 019O "naturality of pointwise minimum on the simplicial interval"]
theorem naturality {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[1]).map f ≫ SSet.deltaOne.min.app n =
      SSet.deltaOne.min.app m ≫ (Δ[1] : SSet.{u}).map f := sorry

end app

/-- Lemma 14.26.8: pointwise minimum as a simplicial map
`Δ[1] ⊗ Δ[1] ⟶ Δ[1]`. -/
@[stacks 019O "pointwise minimum on the simplicial interval"]
noncomputable def map :
    ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⟶ (Δ[1] : SSet.{u}) where
  app := SSet.deltaOne.min.app
  naturality := fun {_ _} f => SSet.deltaOne.min.app.naturality f

namespace map

/-- Evaluation of the pointwise-minimum simplicial map. -/
@[simp, stacks 019O "pointwise-minimum simplicial map formula"]
theorem app_apply (m : SimplexCategoryᵒᵖ)
    (z : ((Δ[1] : SSet.{u}) ⊗ Δ[1]).obj m)
    (k : Fin (m.unop.len + 1)) :
    asOrderHom (SSet.deltaOne.min.map.app m z) k =
      min (asOrderHom z.1 k) (asOrderHom z.2 k) := sorry

/-- At time zero, pointwise minimum is the constant-zero endomorphism of `Δ[1]`. -/
@[reassoc, stacks 019O "pointwise minimum at the zero endpoint"]
theorem ι₀_comp :
    ι₀ ≫ SSet.deltaOne.min.map = SSet.deltaOne.const (0 : Fin 2) := sorry

/-- At time one, pointwise minimum is the identity of `Δ[1]`. -/
@[reassoc, stacks 019O "pointwise minimum at the one endpoint"]
theorem ι₁_comp :
    ι₁ ≫ SSet.deltaOne.min.map = 𝟙 (Δ[1] : SSet.{u}) := sorry

end map

end min

end deltaOne

end SSet
