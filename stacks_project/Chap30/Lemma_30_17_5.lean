module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.ClosedImmersion

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 30.17.5

Let `i : Z ⟶ X` be a closed immersion of Noetherian schemes inducing a
homeomorphism of underlying topological spaces. For an invertible module `L` on
`X`, its pullback to `Z` is ample if and only if `L` is ample.
-/
@[stacks 09MS] #check
  (AlgebraicGeometry.Scheme.Modules.isAmple_pullback_iff_of_isClosedImmersion_isHomeomorph_of_isNoetherian :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) (_ : IsHomeomorph i)
      (L : X.Modules) [IsNoetherian X] [IsNoetherian Z]
      [IsClosedImmersion i] [Scheme.Modules.Invertible L],
      Scheme.Modules.IsAmple ((Scheme.Modules.pullback i).obj L) ↔
        Scheme.Modules.IsAmple L)
