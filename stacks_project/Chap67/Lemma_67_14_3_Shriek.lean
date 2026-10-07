module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import stacks_project.Chap67.Lemma_67_11_2_Pushforward
public import stacks_project.Chap67.Lemma_67_13_3
public import stacks_project.Chap67.Lemma_67_13_4

/-!
# Exceptional inverse image on quasi-coherent modules

Along a closed immersion of algebraic spaces, quasi-coherent pushforward admits a
right adjoint. This file owns that exceptional inverse image and the resulting
adjunction.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

variable {S : Scheme.{u}} {X Z : AlgebraicSpace S}

/-- Pushforward of quasi-coherent modules along a closed immersion of algebraic
spaces admits a right adjoint. -/
instance pushforward_isLeftAdjoint (i : Z ⟶ X) [IsClosedImmersion i] :
    (pushforward i).IsLeftAdjoint := sorry

/-- The exceptional inverse image on quasi-coherent modules along a closed
immersion of algebraic spaces. -/
noncomputable def shriek (i : Z ⟶ X) [IsClosedImmersion i] :
    QCoh X ⥤ QCoh Z :=
  (pushforward i).rightAdjoint

/-- The canonical adjunction between closed-immersion quasi-coherent pushforward
and exceptional inverse image. -/
noncomputable def pushforwardShriekAdjunction (i : Z ⟶ X) [IsClosedImmersion i] :
    pushforward i ⊣ shriek i :=
  Adjunction.ofIsLeftAdjoint (pushforward i)

end AlgebraicGeometry.AlgebraicSpace.QCoh
