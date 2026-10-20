/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.DescentDatum
import StacksCheckRecall

@[expose] public section

universe u v w x

/- Definition 35.3.1 (1): an `A`-module descent datum for `R → A` consists of an
`A ⊗[R] A`-linear equivalence whose three extensions satisfy the cocycle condition. -/
@[stacks 023G] #check (@Module.DescentDatum :
  (R : Type u) → (A : Type v) → (N : Type w) →
    [CommRing R] → [CommRing A] → [Algebra R A] →
      [AddCommGroup N] → [Module R N] → [Module A N] →
        [IsScalarTower R A N] → [SMulCommClass R A N] → Type (max v w))

/- Definition 35.3.1 (2): a morphism of module descent data is an `A`-linear map
commuting with the two descent equivalences. -/
@[stacks 023G] #check (@Module.DescentDatum.Hom :
  {R : Type u} → {A : Type v} → {N : Type w} → {N' : Type x} →
    [CommRing R] → [CommRing A] → [Algebra R A] →
      [AddCommGroup N] → [Module R N] → [Module A N] →
        [IsScalarTower R A N] → [SMulCommClass R A N] →
          [AddCommGroup N'] → [Module R N'] → [Module A N'] →
            [IsScalarTower R A N'] → [SMulCommClass R A N'] →
              Module.DescentDatum R A N → Module.DescentDatum R A N' → Type (max w x))
