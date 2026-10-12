/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.IrreducibleComponents

@[expose] public section

open CommRingCat CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

noncomputable section

/- Lemma 33.8.4 (038F): if `X` is geometrically irreducible over a field `k`, then the second
projection `X ×[Spec (CommRingCat.of k)] Y ⟶ Y` induces the canonical equivalence on irreducible
components. -/
@[stacks 038F] #check
  (@AlgebraicGeometry.GeometricallyIrreducible.pullbackSndComponentsEquiv :
    ∀ {k : Type u} [Field k] {X Y : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
      [GeometricallyIrreducible f],
      irreducibleComponents (pullback f g : Scheme.{u}) ≃ irreducibleComponents Y)

#check
  (@AlgebraicGeometry.GeometricallyIrreducible.pullbackSndComponentsEquiv_def :
    ∀ {k : Type u} [Field k] {X Y : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
      [GeometricallyIrreducible f],
      AlgebraicGeometry.GeometricallyIrreducible.pullbackSndComponentsEquiv f g =
        (pullback.snd f g).irreducibleComponentsEquiv (pullback.snd f g).isOpenMap)

end

end AlgebraicGeometry
