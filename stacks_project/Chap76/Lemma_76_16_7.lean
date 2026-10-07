module

public import stacks_project.Chap67.Lemma_67_38_8_Unramified
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap76.Lemma_76_16_4_FormallyEtale

/-!
# Unramified flat morphisms of algebraic spaces are formally étale
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.16.7: An unramified flat morphism is formally étale. -/
@[stacks 0615]
instance Unramified.toFormallyEtale {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Unramified f] [Flat f] : FormallyEtale f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
