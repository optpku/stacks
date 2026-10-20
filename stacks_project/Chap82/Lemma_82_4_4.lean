module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Length.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Relative

/-!
# Finite nonzero length at a point of a coherent module on a locally Noetherian algebraic space

On a locally Noetherian algebraic space, finite nonzero length of a coherent module at a point
is equivalent to the existence, and to the universality, of an étale scheme chart on which the
point is a generic point of an irreducible component of the support. If the space is decent,
this is also equivalent to the same condition on `|X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]

/- Lemma 82.4.4 (1): Let `S` be a scheme and let `X` be a locally Noetherian algebraic space
over `S`. Let `F` be a coherent `𝒪_X`-module. Let `x ∈ |X|`. The following are equivalent:
there exists an étale morphism `φ : ofOver U ⟶ X` from a scheme and a point `u : U.left`
mapping to `x` which is a generic point of an irreducible component of
`Scheme.Modules.moduleSupport (etaleSchemeModule φ F)`; this holds for every such étale chart
and point over `x`; and `hasFiniteNonzeroLengthAt F x`. -/
@[stacks 0EE4]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.hasFiniteNonzeroLengthAt_tfae :
  ∀ (F : X.Modules) [F.IsCoherent] (x : Points X),
    List.TFAE
      [∃ (U : Over S) (φ : ofOver U ⟶ X),
          Etale φ ∧ ∃ u : U.left,
            Points.mapOfOver φ u = x ∧
              IsGenericPoint.ofIrreducibleComponent u
                (Scheme.Modules.moduleSupport (etaleSchemeModule φ F)),
        ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ] (u : U.left),
          Points.mapOfOver φ u = x →
            IsGenericPoint.ofIrreducibleComponent u
              (Scheme.Modules.moduleSupport (etaleSchemeModule φ F)),
        hasFiniteNonzeroLengthAt F x])

/- Lemma 82.4.4 (2): Let `S` be a scheme and let `X` be a locally Noetherian algebraic space
over `S`. Let `F` be a coherent `𝒪_X`-module. Let `x ∈ |X|`. If `X` is decent, then the three
conditions of `hasFiniteNonzeroLengthAt_tfae` are also equivalent to `x` being a generic point
of an irreducible component of `moduleSupport F`. In this locally Noetherian setting, decent is
equivalent to (absolutely) quasi-separated, by
`IsAbsolutelyQuasiSeparated.of_isLocallyNoetherian_isDecent` and
`instIsDecent_of_isQuasiSeparated`. -/
@[stacks 0EE4]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.hasFiniteNonzeroLengthAt_tfae_of_isDecent :
  ∀ [IsDecent X] (F : X.Modules) [F.IsCoherent]
    (x : Points X),
    List.TFAE
      [∃ (U : Over S) (φ : ofOver U ⟶ X),
          Etale φ ∧ ∃ u : U.left,
            Points.mapOfOver φ u = x ∧
              IsGenericPoint.ofIrreducibleComponent u
                (Scheme.Modules.moduleSupport (etaleSchemeModule φ F)),
        ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ] (u : U.left),
          Points.mapOfOver φ u = x →
            IsGenericPoint.ofIrreducibleComponent u
              (Scheme.Modules.moduleSupport (etaleSchemeModule φ F)),
        hasFiniteNonzeroLengthAt F x,
        IsGenericPoint.ofIrreducibleComponent x (moduleSupport F)])

end AlgebraicGeometry.AlgebraicSpace.Modules
