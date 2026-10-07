module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap69.Lemma_69_19_2_DVR

/-!
# Lemma 69.19.2

A finite-type quasi-separated morphism of algebraic spaces into a locally
Noetherian algebraic space is proper as soon as every DVR valuative square has
a unique lift.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Proper

/-- Lemma 69.19.2: If `f : X ⟶ Y` is a morphism of algebraic spaces over a scheme
`S`, `Y` is locally Noetherian, `f` is of finite type and quasi-separated, and
every DVR valuative square has a unique lift, then `f` is proper. -/
@[stacks 0ARK]
instance of_dvr {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [FiniteType f] [QuasiSeparated f]
    [ValuativeCriterion.DVR f] : Proper f :=
  sorry

end Proper

end AlgebraicGeometry.AlgebraicSpace
