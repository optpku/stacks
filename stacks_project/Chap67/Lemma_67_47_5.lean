module

public import stacks_project.Chap67.Lemma_67_47_5_Domain
public import stacks_project.Chap67.Lemma_67_47_5_PartialMap

/-!
# Lemma 67.47.5

A rational map from a reduced algebraic space to a separated algebraic space
is represented by a unique morphism on its domain of definition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace RationalMap

/-- Lemma 67.47.5 (1): a rational map from a reduced algebraic space `X` to a
separated algebraic space `Y` over a scheme `S` is represented by the
canonical morphism on its domain of definition `U ⊂ X`. -/
@[stacks 0EMR]
theorem toRationalMap_toPartialMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsReduced X] [IsSeparated Y] (φ : RationalMap X Y) :
    φ.toPartialMap.toRationalMap = φ :=
  sorry

/-- Lemma 67.47.5 (2): a morphism on the domain of definition of a rational map
from a reduced algebraic space to a separated algebraic space that represents
that rational map equals the canonical representing morphism. -/
@[stacks 0EMR]
theorem eq_toPartialMap_hom_of_toRationalMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsReduced X] [IsSeparated Y] (φ : RationalMap X Y)
    (f : φ.domainSite.left ⟶ Y)
    (hf : (⟨φ.domainSite, dense_domainSite φ, f⟩ : PartialMap X Y).toRationalMap = φ) :
    f = φ.toPartialMap.hom :=
  sorry

end RationalMap

end AlgebraicGeometry.AlgebraicSpace
