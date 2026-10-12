/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation

/-!
# Locally Noetherian targets upgrade finite type to finite presentation
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.28.7 (1): A morphism of algebraic spaces which is locally of finite
type, with locally Noetherian target, is locally of finite presentation. -/
@[stacks 06G4]
instance locallyOfFinitePresentation_of_locallyOfFiniteType {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] : LocallyOfFinitePresentation f :=
  sorry

/-- Lemma 67.28.7 (2): A morphism of algebraic spaces which is of finite type
and quasi-separated, with locally Noetherian target, is of finite
presentation. -/
@[stacks 06G4]
instance finitePresentation_of_finiteType {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsLocallyNoetherian Y]
    [FiniteType f] [QuasiSeparated f] : FinitePresentation f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
