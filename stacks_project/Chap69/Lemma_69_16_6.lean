module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap69.Lemma_69_16_2_ToSpec
public import stacks_project.Chap69.Situation_69_16_1

/-!
# Lemma 69.16.6

In Situation 69.16.1, the canonical morphism `toSpecGamma X : X ⟶ specGamma X`
is separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 69.16.6: in Situation 69.16.1, the canonical morphism
`toSpecGamma X : X ⟶ specGamma X` is separated. -/
@[stacks 07V5]
instance separated_toSpecGamma {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X] : Separated (toSpecGamma X) :=
  sorry

/-- In Situation 69.16.1, `X` is a separated algebraic space. -/
instance isAbsolutelySeparated_of_hasVanishingH1 {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X] : IsAbsolutelySeparated X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
