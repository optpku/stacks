/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernPolynomial.Newton.ExactSequence
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChernPolynomial.Newton

/- Lemma 42.45.2: For a short exact sequence of finite locally free modules, the
degree-`i` Newton value satisfies `Pᵢ(C.X₂) = Pᵢ(C.X₁) + Pᵢ(C.X₃)`. This integral
identity gives componentwise additivity of the Chern character after rationalization. -/
@[stacks 0F9C] #check (AlgebraicGeometry.ChernPolynomial.Newton.value_eq_add_of_shortExact :
    ∀ {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (classes : ChernClass.Theory δ p) (C : ShortComplex X.Modules)
    [C.X₁.IsFiniteLocallyFree] [C.X₂.IsFiniteLocallyFree] [C.X₃.IsFiniteLocallyFree]
    (hC : C.ShortExact) (i : ℕ),
    value δ p classes C.X₂ i =
      value δ p classes C.X₁ i + value δ p classes C.X₃ i)

end AlgebraicGeometry.ChernPolynomial.Newton
