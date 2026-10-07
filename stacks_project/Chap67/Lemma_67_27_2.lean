module

public import stacks_project.Chap67.Lemma_67_27_2_Locus
public import stacks_project.Chap67.Lemma_67_27_2_Pullback
import StacksCheckRecall

/-!
# Base change of the quasi-finite locus

For a locally of finite type morphism of algebraic spaces, the quasi-finite
locus is open and commutes with base change. Locally quasi-finite morphisms
in the Stacks sense, and quasi-finite morphisms, are stable under base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.27.2 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is locally of finite type. The set of points
of `X` at which `f` is quasi-finite is open. The same holds for any base
change of `f`. -/
@[stacks 0ABM] #check isOpen_quasiFiniteAt

/- Lemma 67.27.2 (2): Formation of the locus where `f` is quasi-finite commutes
with base change: if `g' : X' ⟶ X` is the projection and `f' : X' ⟶ Y'` is the
base change of `f` along `g : Y' ⟶ Y`, then the quasi-finite locus of `f'` is
the preimage of the quasi-finite locus of `f`. -/
@[stacks 0ABM] #check quasiFiniteAt_locus_eq_preimage_of_isPullback

/-- Lemma 67.27.2 (3): The base change of a locally quasi-finite morphism of
algebraic spaces is locally quasi-finite. -/
@[stacks 0ABM]
instance locallyQuasiFinite_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
        MorphismProperty (AlgebraicSpace S)) := sorry

/-- Lemma 67.27.2 (4): The base change of a quasi-finite morphism of algebraic
spaces is quasi-finite. -/
@[stacks 0ABM]
instance quasiFinite_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@QuasiFinite S : MorphismProperty (AlgebraicSpace S)) := sorry

#check LocallyQuasiFinite.pullback_snd
#check QuasiFinite.pullback_snd

end AlgebraicGeometry.AlgebraicSpace
