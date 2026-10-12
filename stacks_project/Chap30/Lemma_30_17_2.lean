/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Finite
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 30.17.2: let `R` be a Noetherian ring, let `f : Y ⟶ X` be a finite surjective
morphism of schemes proper over `R`, and let `L` be an invertible `𝒪_X`-module. Then
`L` is ample if and only if `f^* L` is ample. -/
@[stacks 0B5V] #check
  (AlgebraicGeometry.Scheme.Modules.isAmple_iff_pullback_isAmple_of_isFinite_surjective_properOver :
    ∀ {X Y : Scheme.{u}} {R : Type u} [CommRing R] [IsNoetherianRing R]
      [X.Over (Spec (CommRingCat.of R))] [Y.Over (Spec (CommRingCat.of R))]
      [IsProper (X ↘ Spec (CommRingCat.of R))] [IsProper (Y ↘ Spec (CommRingCat.of R))]
      (f : Y ⟶ X) [IsFinite f] [Surjective f]
      (L : X.Modules) [Scheme.Modules.Invertible L],
      Scheme.Modules.IsAmple L ↔
        Scheme.Modules.IsAmple ((Scheme.Modules.pullback f).obj L))
