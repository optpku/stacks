module

import StacksCheckRecall
public import stacks_project.Chap75.Lemma_75_26_3_FiberEulerCharacteristic

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 75.26.3: if `S` is a scheme, `X` is an algebraic space over `S`, and `E` in
`D(𝒪_X)` is perfect, then the Euler characteristic of the derived residue-field fiber of
`E` is locally constant on `Points X`. -/
@[stacks 0D1Z] #check
  (ModuleDerived.fiberEulerChar_isLocallyConstant :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (E : ModuleDerived X),
      ModuleDerived.IsPerfect E →
        IsLocallyConstant (ModuleDerived.fiberEulerChar E))
