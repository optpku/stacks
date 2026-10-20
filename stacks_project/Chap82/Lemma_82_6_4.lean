module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedCycle.Additivity

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
  AlgebraicGeometry.AlgebraicSpace.Hom

universe u

/- Lemma 82.6.4: In Situation 82.2.1, let `X / B` be good. Let
`0 ⟶ F ⟶ G ⟶ H ⟶ 0` be a short exact sequence of coherent `𝒪_X`-modules,
packaged as `C : ShortComplex X.Modules` with `hC : C.ShortExact`, `F = C.X₁`,
`G = C.X₂`, `H = C.X₃`, and maps `C.f`, `C.g`. Assume `dim_δ(Supp(F))`,
`dim_δ(Supp(G))`, and `dim_δ(Supp(H))` are `≤ k`. Then `[G]_k = [F]_k + [H]_k`. -/
@[stacks 0EEE] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.moduleCycle_eq_add_of_shortExact :
    {S : Scheme.{u}} → {B X : AlgebraicSpace S} → [UniversallyCatenary B] →
    [IsQuasiSeparated B] → (f : X ⟶ B) → [QuasiSeparated f] → [LocallyOfFiniteType f] →
    (δ : Points B → ℤ) → [IsDimensionFunction δ] → (C : ShortComplex X.Modules) →
    [C.X₁.IsCoherent] → [C.X₂.IsCoherent] → [C.X₃.IsCoherent] → (hC : C.ShortExact) →
    (k : ℤ) → (h₁ : moduleSupportDeltaDimension f δ C.X₁ ≤ (k : EInt)) →
    (h₂ : moduleSupportDeltaDimension f δ C.X₂ ≤ (k : EInt)) →
    (h₃ : moduleSupportDeltaDimension f δ C.X₃ ≤ (k : EInt)) →
    moduleCycle f δ C.X₂ k h₂ =
      moduleCycle f δ C.X₁ k h₁ + moduleCycle f δ C.X₃ k h₃)
