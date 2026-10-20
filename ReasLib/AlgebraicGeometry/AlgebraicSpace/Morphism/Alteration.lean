/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Alteration
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dominant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.GenericallyFinite.Integral

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

/-- For a proper dominant morphism of integral algebraic spaces, being an
alteration is equivalent to the generic residue-field, finite affine restriction,
quasi-finiteness, singleton generic-fibre, and finite affine target-open conditions. -/
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

/-- A proper surjective morphism of algebraic spaces onto an integral target
restricts to an alteration along some integral closed subspace of its source. -/
theorem exists_integralClosedSubspace_isAlteration
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsIntegral Y]
    (f : X ⟶ Y) [Proper f] [Surjective f] :
    ∃ (X' : ClosedSubspace X) (hX' : IsIntegral X'.X),
      IsAlteration (X'.ι ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
