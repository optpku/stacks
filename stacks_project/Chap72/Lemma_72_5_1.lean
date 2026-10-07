module

public import Mathlib.Data.List.TFAE
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_18_1_Dominant
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_27_6_LocallyQuasiFinite
public import stacks_project.Chap67.Lemma_67_33_3_ResidueFieldTrdeg
public import stacks_project.Chap68.Definition_68_22_1_GenericPoints
public import stacks_project.Chap72.Definition_72_4_1_Integral
public import stacks_project.Chap76.Lemma_76_36_2_PointsOver

/-!
# Generically finite morphisms of integral algebraic spaces

A dominant locally finite type morphism of integral algebraic spaces is
generically finite in several equivalent senses: residue-field transcendence
degree zero, a finite residue-field extension at the generic point, a finite
restriction between nonempty affine opens, quasi-finiteness at the generic
point, and a singleton generic fibre. If the morphism is quasi-compact or
separated, this is also equivalent to finiteness over a nonempty affine open
of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 72.5.1 (1): Let `S` be a scheme. Let `X` and `Y` be integral algebraic
spaces over `S`. Let `x` be a generic point of `Points X`, and write `y` for
`Points.map f x`, the generic point of `Points Y`. Let `f : X ⟶ Y` be locally
of finite type and dominant. The following are equivalent: the residue-field
transcendence degree of `x / y` is `0`; the extension
`X.residueField x / Y.residueField y` is finite; there exist nonempty affine
opens `U ⊂ X` and `V ⊂ Y` and a finite restriction `g : U.X ⟶ V.X` with
`g ≫ V.ι = U.ι ≫ f`; `f` is quasi-finite at `x`; and `x` is the only point of
`Points X` mapping to `y`. -/
@[stacks 0AD5]
theorem genericallyFinite_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f]
    [Dominant f] {x : Points X} (hx : x ∈ genericPoints X) :
    List.TFAE
      [ residueFieldTrdegAt f x = 0
      , FiniteDimensional (Y.residueField (Points.map f x)) (X.residueField x)
      , ∃ (U : OpenSubspace X) (V : OpenSubspace Y) (g : U.X ⟶ V.X),
          U.pointsSet.Nonempty ∧ V.pointsSet.Nonempty ∧ IsAffine U.X ∧
            IsAffine V.X ∧ g ≫ V.ι = U.ι ≫ f ∧ IsFinite g
      , QuasiFiniteAt f x
      , Points.map f ⁻¹' {Points.map f x} = {x} ] :=
  sorry

/-- Lemma 72.5.1 (2): Let `S` be a scheme. Let `X` and `Y` be integral algebraic
spaces over `S`. Let `x` be a generic point of `Points X`, and write `y` for
`Points.map f x`. Let `f : X ⟶ Y` be locally of finite type and dominant, and
assume `f` is quasi-compact or separated. Then the conditions of
`genericallyFinite_tfae` are also equivalent to the existence of a nonempty
affine open `V ⊂ Y` such that `pullback.snd f V.ι` is finite. -/
@[stacks 0AD5]
theorem genericallyFinite_tfae_of_quasiCompact_or_separated
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [Dominant f] {x : Points X}
    (hx : x ∈ genericPoints X) (hqc_or_sep : QuasiCompact f ∨ Separated f) :
    List.TFAE
      [ residueFieldTrdegAt f x = 0
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

/-- A dominant morphism of irreducible decent algebraic spaces sends a generic
point of the source to a generic point of the target. -/
theorem map_mem_genericPoints_of_isDominant {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y] [IsIrreducible X]
    [IsIrreducible Y] (f : X ⟶ Y) [Dominant f] {x : Points X}
    (hx : x ∈ genericPoints X) : Points.map f x ∈ genericPoints Y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
