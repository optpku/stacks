module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Alteration
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap67.Definition_67_18_1_Dominant
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap72.Definition_72_4_1_Integral

/-!
# Alterations of integral algebraic spaces

An alteration is a proper dominant morphism of integral algebraic spaces that
is finite over some nonempty open subspace of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An alteration is a proper dominant morphism between integral algebraic
spaces that is finite over some nonempty open of the target. -/
class IsAlteration {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    [IsIntegral Y] [IsIntegral X] (f : Y ⟶ X) : Prop
    extends Proper f, Dominant f where
  /-- The alteration is finite over some nonempty open subspace of the target. -/
  exists_nonempty_open_isFinite :
    ∃ U : OpenSubspace X, U.pointsSet.Nonempty ∧ IsFinite (pullback.snd f U.ι)

/-- Over integral source and target algebraic spaces, a morphism is an
alteration if and only if it is proper, dominant, and finite over some
nonempty open of the target. -/
theorem isAlteration_iff {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    [IsIntegral Y] [IsIntegral X] (f : Y ⟶ X) :
    IsAlteration f ↔
      Proper f ∧ Dominant f ∧
        ∃ U : OpenSubspace X, U.pointsSet.Nonempty ∧
          IsFinite (pullback.snd f U.ι) :=
  sorry

/-- The identity morphism of an integral algebraic space is an alteration. -/
instance instIsAlteration_id {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsIntegral X] : IsAlteration (𝟙 X) :=
  sorry

/-- An alteration of schemes over `S` induces an alteration of the associated
algebraic spaces. -/
instance instIsAlteration_ofOverMap {S : Scheme.{u}} {U V : Over S}
    (f : U ⟶ V) [AlgebraicGeometry.IsIntegral U.left]
    [AlgebraicGeometry.IsIntegral V.left]
    [AlgebraicGeometry.IsAlteration f.left] :
    IsAlteration (ofOverMap f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
