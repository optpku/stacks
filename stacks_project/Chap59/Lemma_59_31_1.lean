/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Subterminal
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry

universe u

/- Lemma 59.31.1 (04HV): a subsheaf of the final object in the small étale topos of a scheme is
represented by a unique open subscheme. -/
@[stacks 04HV] #check (@AlgebraicGeometry.Scheme.existsUnique_open_of_mono_terminal :
    ∀ (S : Scheme.{u}) [HasWeakSheafify S.smallEtaleTopology (Type (u + 1))]
      (F : Sheaf S.smallEtaleTopology (Type (u + 1))) [Mono (terminal.from F)],
      ∃! W : S.Opens,
        Nonempty (F ≅
          S.smallEtaleTopology.sheafifiedRepresentable (Scheme.Etale.mk W.ι)))
