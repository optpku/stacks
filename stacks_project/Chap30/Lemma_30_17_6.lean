/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiAffine.ClosedImmersion
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 30.17.6: let `i : Z ⟶ X` be a closed immersion of Noetherian schemes inducing a
homeomorphism of underlying topological spaces. Then `X` is quasi-affine if and only if `Z` is
quasi-affine. -/
@[stacks 0B7K] #check
  (AlgebraicGeometry.Scheme.isQuasiAffine_iff_of_isClosedImmersion_isHomeomorph_of_isNoetherian :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsNoetherian X] [IsNoetherian Z]
      [IsClosedImmersion i] (hi : IsHomeomorph i),
      X.IsQuasiAffine ↔ Z.IsQuasiAffine)
