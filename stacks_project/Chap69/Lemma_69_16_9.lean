module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.AmpleCriterion
public import stacks_project.Chap69.Lemma_69_20_1_Tensor
import StacksCheckRecall

/-!
# Lemma 69.16.9

A Noetherian algebraic space with vanishing `H¹` of positive twists of every coherent
module by an invertible sheaf is a scheme, and the invertible sheaf is ample on every
representing scheme.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 69.16.9: a Noetherian algebraic space satisfying positive-twist first-cohomology
vanishing for every coherent module is a scheme, and the invertible module is ample. -/
@[stacks 0D2W] #check
  (AlgebraicGeometry.AlgebraicSpace.isScheme_and_isAmpleObject_of_coherent_h1_twist_zero :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsNoetherian X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    (L : X.Modules) [isInvertibleObject L],
    (∀ (F : Modules X) [F.IsCoherent],
      ∃ n : ℕ, 0 < n ∧ IsZero (cohomology X (F ⊗ tensorPower L n) 1)) →
    IsScheme X ∧ ∀ {T : Over S} (e : X ≅ ofOver T),
      Scheme.Modules.isAmpleObject (Modules.toSchemeModule e L))
