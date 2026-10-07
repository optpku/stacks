module

public import stacks_project.Chap66.Lemma_66_25_4_Regular
public import stacks_project.Chap67.Lemma_67_49_2
public import stacks_project.Chap67.Lemma_67_49_5_Normalization
public import stacks_project.Chap72.Definition_72_8_3_Alteration

/-!
# Regular alterations imply finite normalization

A Noetherian integral algebraic space admitting an alteration from a regular
algebraic space has finite absolute normalization and a dense regular open
subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsAlteration

/-- Lemma 89.7.1 (1) Let `S` be a scheme. Let `Y` be a Noetherian integral
algebraic space over `S`. If `f : X ⟶ Y` is an alteration with `X` regular,
then the normalization `Y.normalizationTo : Y.normalization ⟶ Y` is finite. -/
@[stacks 0BHT]
theorem isFinite_normalizationTo {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsNoetherian Y] [IsIntegral Y] [IsIntegral X] (f : X ⟶ Y)
    [IsAlteration f] [IsRegular X] : IsFinite Y.normalizationTo :=
  sorry

/-- Lemma 89.7.1 (2) Let `S` be a scheme. Let `Y` be a Noetherian integral
algebraic space over `S`. If `f : X ⟶ Y` is an alteration with `X` regular,
then `Y` has a dense open subspace which is regular. -/
@[stacks 0BHT]
theorem exists_dense_open_regular {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsNoetherian Y] [IsIntegral Y] [IsIntegral X] (f : X ⟶ Y)
    [IsAlteration f] [IsRegular X] :
    ∃ U : OpenSubspace Y, Dense (U.pointsSet : Set (Points Y)) ∧ IsRegular U.X :=
  sorry

end IsAlteration

end AlgebraicGeometry.AlgebraicSpace
