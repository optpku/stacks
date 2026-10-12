/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Abelian.Basic
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent.Preadditive

/-!
# Abelian structure on equivariant quasi-coherent modules

Flat source and target morphisms make kernels and cokernels of equivariant
quasi-coherent modules compatible with the groupoid action.
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace AlgebraicGeometry.GroupoidScheme.QCoh

/-- If the source and target morphisms of a groupoid scheme are flat, its category of
equivariant quasi-coherent modules is abelian. -/
@[reducible]
def abelian {S : Scheme.{u}} (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left] : Abelian G.QCoh where
  toPreadditive := preadditive G
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry
  has_kernels := sorry
  has_cokernels := sorry

end AlgebraicGeometry.GroupoidScheme.QCoh
