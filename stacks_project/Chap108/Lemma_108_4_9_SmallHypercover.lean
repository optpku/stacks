/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.OneHypercoverDense

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site

variable {D : Type u} [Category.{u} D] {C : Type v} [Category.{u} C]
  (F : D ⥤ C) (J₀ : GrothendieckTopology D) (J : GrothendieckTopology C)
  [F.IsCoverDense J]

/-- Small hypercover data enumerating actual chart maps and commuting pairs.
It does not choose an ambient pullback or use an admitted limit-existence instance. -/
def smallHypercoverData (S : C) : F.OneHypercoverDenseData.{u} J₀ J S where
  I₀ := Σ d : D, F.obj d ⟶ S
  X i := i.1
  f i := i.2
  I₁ i j := Σ d : D,
    {pair : (d ⟶ i.1) × (d ⟶ j.1) // F.map pair.1 ≫ i.2 = F.map pair.2 ≫ j.2}
  Y {_ _} j := j.1
  p₁ {_ _} j := j.2.1.1
  p₂ {_ _} j := j.2.1.2
  w {_ _} j := j.2.2
  mem₀ := by
    apply J.superset_covering _ (F.is_cover_of_isCoverDense J S)
    rintro W k ⟨⟨d, a, b, hab⟩⟩
    exact ⟨F.obj d, a, b, ⟨(⟨d, b⟩ : Σ d : D, F.obj d ⟶ S)⟩, hab⟩
  mem₁₀ i j W p₁ p₂ h := by
    apply J₀.covering_of_eq_top
    apply Sieve.id_mem_iff_eq_top.mp
    exact ⟨⟨W, ⟨(p₁, p₂), h⟩⟩, 𝟙 W, rfl, rfl⟩

/-- The small hypercover certificate is proved from the explicit data above. -/
theorem smallOneHypercoverDense : F.IsOneHypercoverDense.{u} J₀ J where
  nonempty_oneHypercoverDenseData S := ⟨smallHypercoverData F J₀ J S⟩

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site
