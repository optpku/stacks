module

public import Mathlib.Data.List.TFAE
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap72.Definition_72_8_3_Alteration
public import stacks_project.Chap72.Lemma_72_5_1

/-!
# Alterations and generically finite morphisms

A proper dominant morphism of integral algebraic spaces is an alteration if
and only if it satisfies any of the equivalent generically finite conditions
of Lemma 72.5.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 72.8.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a proper dominant
morphism of integral algebraic spaces over `S`. Then `f` is an alteration if
and only if any of the equivalent conditions (1)–(6) of Lemma 72.5.1 hold. -/
@[stacks 0ADB]
theorem isAlteration_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [Proper f] [Dominant f]
    {x : Points X} (hx : x ∈ genericPoints X) :
    List.TFAE
      [ IsAlteration f
      , residueFieldTrdegAt f x = 0
      , FiniteDimensional (Y.residueField (Points.map f x)) (X.residueField x)
      , ∃ (U : OpenSubspace X) (V : OpenSubspace Y) (g : U.X ⟶ V.X),
          U.pointsSet.Nonempty ∧ V.pointsSet.Nonempty ∧ IsAffine U.X ∧
            IsAffine V.X ∧ g ≫ V.ι = U.ι ≫ f ∧ IsFinite g
      , QuasiFiniteAt f x
      , Points.map f ⁻¹' {Points.map f x} = {x}
      , ∃ V : OpenSubspace Y,
          V.pointsSet.Nonempty ∧ IsAffine V.X ∧
            IsFinite (pullback.snd f V.ι) ] :=
  sorry

/-- A proper dominant morphism of integral algebraic spaces is an alteration
if and only if the residue-field transcendence degree at a generic point is
`0`. -/
theorem isAlteration_iff_residueFieldTrdegAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [Proper f] [Dominant f] {x : Points X} (hx : x ∈ genericPoints X) :
    IsAlteration f ↔ residueFieldTrdegAt f x = 0 :=
  sorry

/-- A proper dominant morphism of integral algebraic spaces is an alteration
if and only if it is finite over some nonempty affine open of the target. -/
theorem isAlteration_iff_exists_isAffine_isFinite {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [Proper f] [Dominant f] :
    IsAlteration f ↔
      ∃ V : OpenSubspace Y,
        V.pointsSet.Nonempty ∧ IsAffine V.X ∧
          IsFinite (pullback.snd f V.ι) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
