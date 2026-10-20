module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.GenericPoints
import StacksCheckRecall

/-!
# Finite neighbourhoods in codimension at most one

The four generic-finiteness criteria for a proper morphism to be finite over
an open neighbourhood of a point of codimension at most one.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 72.3.2 (1): Vanishing residue-field transcendence degree at every codimension-zero point. -/
@[stacks 0AD2]
#check (AlgebraicGeometry.AlgebraicSpace.exists_isFinite_openInverseImageTo_of_residueFieldTrdeg_eq_zero :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    [IsLocallyNoetherian Y] {y : Points Y} (hy : localRingDimAt y ≤ 1)
    (htrdeg : ∀ x : Points X, localRingDimAt x = 0 → ResidueFieldTrdegEqAt f 0 x),
    ∃ (Y' : AlgebraicSpace S) (ι : Y' ⟶ Y) (hι : IsOpenImmersion ι),
      y ∈ Set.range (Points.map ι) ∧ IsFinite (openInverseImageTo f ι))

/- Lemma 72.3.2 (2): Vanishing residue-field transcendence degree at codimension-zero points whose images specialize to the target point. -/
@[stacks 0AD2]
#check (AlgebraicGeometry.AlgebraicSpace.IsFinite.exists_open_of_trdeg_eq_zero_of_specializes :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    [IsLocallyNoetherian Y] {y : Points Y} (hy : localRingDimAt y ≤ 1)
    (htrdeg : ∀ x : Points X, localRingDimAt x = 0 → Points.map f x ⤳ y →
      ResidueFieldTrdegEqAt f 0 x),
    ∃ (Y' : AlgebraicSpace S) (ι : Y' ⟶ Y) (hι : IsOpenImmersion ι),
      y ∈ Set.range (Points.map ι) ∧ IsFinite (openInverseImageTo f ι))

/- Lemma 72.3.2 (3): Quasi-finiteness at every codimension-zero point. -/
@[stacks 0AD2]
#check (AlgebraicGeometry.AlgebraicSpace.exists_isFinite_openInverseImageTo_of_codimZero :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    [IsLocallyNoetherian Y] {y : Points Y} (hy : localRingDimAt y ≤ 1)
    (hqf : ∀ x : Points X, localRingDimAt x = 0 → QuasiFiniteAt f x),
    ∃ (Y' : AlgebraicSpace S) (ι : Y' ⟶ Y) (hι : IsOpenImmersion ι),
      y ∈ Set.range (Points.map ι) ∧ IsFinite (openInverseImageTo f ι))

/- Lemma 72.3.2 (4): Density of the quasi-finite locus. -/
@[stacks 0AD2]
#check (AlgebraicGeometry.AlgebraicSpace.exists_isFinite_openInverseImageTo_of_denseLocus :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    [IsLocallyNoetherian Y] {y : Points Y} (hy : localRingDimAt y ≤ 1)
    (hdense : Dense (setOf fun z : Points X ↦ QuasiFiniteAt f z)),
    ∃ (Y' : AlgebraicSpace S) (ι : Y' ⟶ Y) (hι : IsOpenImmersion ι),
      y ∈ Set.range (Points.map ι) ∧ IsFinite (openInverseImageTo f ι))

end AlgebraicGeometry.AlgebraicSpace
