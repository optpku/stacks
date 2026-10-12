/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import stacks_project.Chap82.Definition_82_6_1_AssociatedCycle

/-!
# Additivity of associated cycles of coherent modules

In the good setup of Situation 82.2.1, the degree-`k` cycle associated to a
coherent `𝒪_X`-module is additive along a short exact sequence when all three
supports have `δ`-dimension at most `k`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Lemma 82.6.4: In Situation 82.2.1, let `X / B` be good. Let
`0 ⟶ F ⟶ G ⟶ H ⟶ 0` be a short exact sequence of coherent `𝒪_X`-modules,
packaged as `C : ShortComplex X.Modules` with `hC : C.ShortExact`, `F = C.X₁`,
`G = C.X₂`, `H = C.X₃`, and maps `C.f`, `C.g`. Assume `dim_δ(Supp(F))`,
`dim_δ(Supp(G))`, and `dim_δ(Supp(H))` are `≤ k`. Then `[G]_k = [F]_k + [H]_k`. -/
@[stacks 0EEE]
theorem moduleCycle_eq_add_of_shortExact
    {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B]
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (C : ShortComplex X.Modules)
    [C.X₁.IsCoherent] [C.X₂.IsCoherent] [C.X₃.IsCoherent] (hC : C.ShortExact)
    (k : ℤ) (h₁ : f.moduleSupportDeltaDimension δ C.X₁ ≤ (k : EInt))
    (h₂ : f.moduleSupportDeltaDimension δ C.X₂ ≤ (k : EInt))
    (h₃ : f.moduleSupportDeltaDimension δ C.X₃ ≤ (k : EInt)) :
    moduleCycle f δ C.X₂ k h₂ =
      moduleCycle f δ C.X₁ k h₁ + moduleCycle f δ C.X₃ k h₃ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
