/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.ClosedImmersion
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 32.11.4

Let `i : Z ⟶ X` be a closed immersion inducing a homeomorphism of underlying
topological spaces. For an invertible module `L` on `X`, its pullback to `Z` is
ample if and only if `L` is ample.
-/
@[stacks 09MW] #check
  (AlgebraicGeometry.Scheme.Modules.isAmple_pullback_iff_of_isClosedImmersion_isHomeomorph :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) (_ : IsHomeomorph i)
      (L : X.Modules) [IsClosedImmersion i] [Scheme.Modules.Invertible L],
      Scheme.Modules.IsAmple ((Scheme.Modules.pullback i).obj L) ↔
        Scheme.Modules.IsAmple L)
