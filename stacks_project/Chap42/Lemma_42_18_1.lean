/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Principal.Pushforward
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 42.18.1: for a dominant proper morphism between integral schemes of the same
`δ`-dimension over a universally catenary base, the pushforward of a principal cycle is the
principal cycle of the induced function-field norm. -/
@[stacks 02RT] #check (AlgebraicGeometry.AlgebraicCycle.map_principal_of_proper :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral X.left] [IsIntegral Y.left] (n : ℤ) (p : X ⟶ Y)
    [IsProper p.left] [IsDominant p.left]
    (hX : X.hom.relativeDimensionFunction δ (genericPoint X.left) = n)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = n)
    (f : X.left.functionFieldˣ),
    -- Local instance justification (proof-local temporary data): local finite type over the locally Noetherian base `S` canonically makes `X.left` locally Noetherian.
    letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    -- Local instance justification (proof-local temporary data): local finite type over the locally Noetherian base `S` canonically makes `Y.left` locally Noetherian.
    letI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
    AlgebraicGeometry.AlgebraicCycle.map p.left
        (X.hom.relativeDimensionFunction δ) (Y.hom.relativeDimensionFunction δ)
        (AlgebraicGeometry.AlgebraicCycle.principal X.left f) =
      AlgebraicGeometry.AlgebraicCycle.principal Y.left
        (p.left.inducedFunctionFieldNorm f))
