module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.AffineCriterion
import StacksCheckRecall

/-!
# Lemma 69.16.8

A Noetherian algebraic space with vanishing `H¹` on every coherent module is an
affine scheme.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 69.16.8: let `S` be a scheme and let `X` be a Noetherian algebraic space over
`S`. If `H¹(X, F) = 0` for every coherent `𝒪_X`-module `F`, then `X` is an affine
scheme. -/
@[stacks 0D2V] #check (AlgebraicGeometry.AlgebraicSpace.isAffine_of_coherent_h1_zero :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsNoetherian X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})],
    (∀ (F : Modules X) [F.IsCoherent], IsZero (cohomology X F 1)) → IsAffine X)

/- On a Noetherian algebraic space, vanishing of `H¹` on every coherent module
implies vanishing of `H¹` on every quasi-coherent module. -/
#check (AlgebraicGeometry.AlgebraicSpace.hasVanishingH1_of_coherent_h1_zero :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsNoetherian X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})],
    (∀ (F : Modules X) [F.IsCoherent], IsZero (cohomology X F 1)) → HasVanishingH1 X)

end AlgebraicGeometry.AlgebraicSpace
