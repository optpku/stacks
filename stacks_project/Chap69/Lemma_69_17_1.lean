/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.FiniteSurjective
import StacksCheckRecall

/-!
# Lemma 69.17.1

The pushforward of the structure sheaf of the inverse image of a closed
immersion along a finite surjective morphism of locally Noetherian algebraic
spaces is a coherent module of full étale-site support.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 69.17.1 (1): if `f : Y ⟶ X` is a finite surjective morphism of algebraic spaces
over a scheme `S` with `X` locally Noetherian, and `i : Z ⟶ X` is a closed immersion,
then `f'_* 𝒪_{Z'}` is a coherent `𝒪_Z`-module, where `Z'` is `inverseImage f i` and
`f'` is `inverseImageTo f i`. -/
@[stacks 0GF7] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.pushforward_inverseImageTo_unit_isCoherent :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) [IsFinite f] [Surjective f]
    [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i],
    ((pushforward (inverseImageTo f i)).obj
        (SheafOfModules.unit (structureSheaf (inverseImage f i)))).IsCoherent)

/- Lemma 69.17.1 (2): under the same hypotheses, the étale-site support of `f'_* 𝒪_{Z'}`
equals `|Z|`. -/
@[stacks 0GF7] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.moduleSupport_pushforward_inverseImageTo_unit_eq_univ :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) [IsFinite f] [Surjective f]
    [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i],
    moduleSupport
        ((pushforward (inverseImageTo f i)).obj
          (SheafOfModules.unit (structureSheaf (inverseImage f i)))) =
      (Set.univ : Set (Points Z)))

end AlgebraicGeometry.AlgebraicSpace.Modules
