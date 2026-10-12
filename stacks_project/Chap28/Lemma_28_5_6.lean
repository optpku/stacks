/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Immersion.Noetherian
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/-
Lemma 28.5.6 (1): any locally closed subscheme of a locally Noetherian scheme is locally
Noetherian. Formally, a locally closed subscheme is represented by an immersion `f : X ⟶ Y`.
-/
@[stacks 02IK] #check (AlgebraicGeometry.IsLocallyNoetherian.of_isImmersion :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] [IsLocallyNoetherian Y],
    IsLocallyNoetherian X)

/-
Lemma 28.5.6 (2): any locally closed subscheme of a Noetherian scheme is Noetherian. Formally, a
locally closed subscheme is represented by an immersion `f : X ⟶ Y`.
-/
@[stacks 02IK] #check (AlgebraicGeometry.IsNoetherian.of_isImmersion :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] [IsNoetherian Y], IsNoetherian X)

-- The compactness input used in the Noetherian transfer is reusable on its own.
#check (AlgebraicGeometry.quasiCompact_of_isImmersion_of_isLocallyNoetherian :
  ∀ {Z X : Scheme.{u}} {f : Z ⟶ X} [IsImmersion f] [IsLocallyNoetherian X], QuasiCompact f)
