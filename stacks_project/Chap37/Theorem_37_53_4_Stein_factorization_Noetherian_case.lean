module

public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stein.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [IsProper f]

/- Theorem 37.53.4 (Stein factorization; Noetherian case) (1): the canonical middle
scheme in the factorization is the normalization of `S` in `X`. -/
@[stacks 03H0] #check (AlgebraicGeometry.Scheme.Hom.normalization f : Scheme.{u})

/- Theorem 37.53.4 (Stein factorization; Noetherian case) (2): the canonical maps
through the normalization compose to `f`. -/
@[stacks 03H0] #check
  (AlgebraicGeometry.Scheme.Hom.toNormalization_fromNormalization f :
    AlgebraicGeometry.Scheme.Hom.toNormalization f ≫
      AlgebraicGeometry.Scheme.Hom.fromNormalization f = f)

/- Theorem 37.53.4 (Stein factorization; Noetherian case) (3): the canonical map from
`X` to the normalization of `S` in `X` is proper. -/
@[stacks 03H0] #check
  (AlgebraicGeometry.Scheme.Hom.instIsProperToNormalizationOfProper f :
    IsProper (AlgebraicGeometry.Scheme.Hom.toNormalization f))

/- Theorem 37.53.4 (Stein factorization; Noetherian case) (4): the canonical map from
`X` to the normalization of `S` in `X` has geometrically connected fibres. -/
@[stacks 03H0] #check
  (AlgebraicGeometry.Scheme.Hom.instGeometricallyConnectedToNormalizationOfProper f :
    GeometricallyConnected (AlgebraicGeometry.Scheme.Hom.toNormalization f))

/- Theorem 37.53.4 (Stein factorization; Noetherian case) (5): the structural morphism
from the normalization of `S` in `X` to `S` is finite. -/
@[stacks 03H0] #check
  (AlgebraicGeometry.Scheme.Hom.instIsFiniteFromNormalizationOfProper f :
    IsFinite (AlgebraicGeometry.Scheme.Hom.fromNormalization f))

/- Theorem 37.53.4 (Stein factorization; Noetherian case) (6): the canonical map
`𝒪_{f.normalization} ⟶ f.toNormalization_* 𝒪_X` is an isomorphism. -/
@[stacks 03H0] #check
  (AlgebraicGeometry.Scheme.Hom.instIsIsoPushforwardMapToNormalization f :
    IsIso (RingedSpace.Hom.commRingSheafPushforwardMap
      (AlgebraicGeometry.Scheme.Hom.toNormalization f).toShHom))

/- Theorem 37.53.4 (Stein factorization; Noetherian case) (7): the structural morphism
from `f.normalization` realizes `Spec_S(f_* 𝒪_X)`. -/
@[stacks 03H0] #check
  (AlgebraicGeometry.Scheme.Hom.fromNormalization_realizesRelativeSpectrum f :
    Scheme.realizesRelativeSpectrum (Scheme.pushforwardStructureSheafQcAlgebra f)
      (AlgebraicGeometry.Scheme.Hom.fromNormalization f))

end AlgebraicGeometry.Scheme.Hom
