module

public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite

/-!
# Étale morphisms of algebraic spaces are locally quasi-finite
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.39.5: An étale morphism of algebraic spaces is locally quasi-finite. -/
@[stacks 03XU]
instance locallyQuasiFinite_of_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] : LocallyQuasiFinite f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
