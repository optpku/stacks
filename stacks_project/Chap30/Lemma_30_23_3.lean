/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Epi
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 30.23.3: for a Noetherian scheme `X` and ideal-sheaf data `I`, a morphism of
coherent formal modules is an epimorphism if and only if its first-stage component is an
epimorphism. -/
@[stacks 087Y] #check
  (AlgebraicGeometry.Scheme.coherentFormalModules_epi_iff_firstStage_epi :
    ∀ {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
      {F G : Scheme.CoherentFormalModules X I} (φ : F ⟶ G),
      Epi φ ↔ Epi (φ.hom.app (Opposite.op 1)))
