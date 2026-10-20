/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSurjective.ClosedImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry FormalAlgebraicSpace
  AffineFormalAlgebraicSpace CategoryTheory.Limits

universe u

/- Lemma 88.21.12: A closed immersion between locally Noetherian formal algebraic
spaces is rig-surjective if and only if every representable étale affine test
has base change induced by a surjection of adic Noetherian rings whose kernel
`J` satisfies `I * J ^ n = ⊥` for an ideal of definition `I` and `0 < n`. -/
@[stacks 0GD5] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective.iff_etaleAffine_kernel :
    ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [ClosedImmersion f],
      RigSurjective f ↔
      ∀ {V : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace V] [IsAffine V]
        (v : V ⟶ Y) [Etale v],
        KernelKilledByPowIdealOfDefinition (pullback.snd f v))
