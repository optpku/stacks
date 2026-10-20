/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPower.ArtinRees
import StacksCheckRecall

/-!
# Lemma 69.13.3 (Artin-Rees)

On a Noetherian algebraic space, a coherent module, a quasi-coherent subsheaf,
and a quasi-coherent ideal sheaf satisfy the Artin–Rees lemma.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

/- Lemma 69.13.3 (Artin-Rees): let `S` be a scheme, let `X` be a Noetherian algebraic
space over `S`, let `F` be a coherent sheaf on `X`, let `G ⊂ F` be a quasi-coherent
subsheaf, and let `I ⊂ 𝒪_X` be a quasi-coherent sheaf of ideals. Then there exists
`c ≥ 0` such that for all `n ≥ c` one has
`I^(n-c)(I^c F ∩ G) = I^n F ∩ G` as subobjects of `F`. -/
@[stacks 07UL] #check (
  AlgebraicGeometry.AlgebraicSpace.Modules.exists_artinReesConstant :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
      (F : X.Modules) [F.IsCoherent] (G : Subobject F)
      [((G : X.Modules)).IsQuasicoherent] (I : IdealSubobject X) [IsQuasiCoherent I],
      ∃ c : ℕ, ∀ n ≥ c,
        idealPowerSmulSubobject I ((idealPowerProductSubobject I F c) ⊓ G) (n - c) =
          idealPowerProductSubobject I F n ⊓ G)
