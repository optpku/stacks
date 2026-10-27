/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverOpen.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePresentation.IsoOverOpen
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Spectrum

/-!
# Base change to the punctured henselization of a decent algebraic space

Slice base change along `fromHenselization` lifts to finite-presentation
iso-over-open slice categories, from the complement of a closed point to the
punctured spectrum of the henselization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Base change along `fromHenselization` preserves finite presentation and being an
isomorphism over the complementary open of a closed point, after restriction to
the punctured henselization. -/
theorem puncturedHenselizationBaseChange_mem {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] {x : Points X}
    (hx : x ∈ closedPoints (Points X))
    [QuasiCompact (closedPointComplementι X hx)]
    (N : EtaleNeighborhood X x)
    (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {x} = {N.point} ∧ N.IsElementary)
    (R : Type u) [CommRing R] [Algebra (N.scheme.presheaf.stalk N.point) R]
    [IsHenselizationOf (N.scheme.presheaf.stalk N.point) R]
    (Y : FinitePresentationIsoOverOpen (closedPointComplementι X hx)) :
    @finitePresentationIsoOverOpenProperty S _ _ (henselizationPuncturedι X x N hN R) (Henselization.isOpenImmersion_puncturedι R (henselizationOver X x N hN R).hom)
      ((overPullback (fromHenselization X x N hN R)).obj Y.obj) :=
  sorry

/-- Base change along `Spec(𝒪_{X,x}^h) ⟶ X` as a functor on finite-presentation
iso-over-open slice categories, from `X \ {x}` to the punctured henselization. -/
def puncturedHenselizationBaseChange {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] {x : Points X} (hx : x ∈ closedPoints (Points X))
    [QuasiCompact (closedPointComplementι X hx)]
    (N : EtaleNeighborhood X x)
    (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {x} = {N.point} ∧ N.IsElementary)
    (R : Type u) [CommRing R] [Algebra (N.scheme.presheaf.stalk N.point) R]
    [IsHenselizationOf (N.scheme.presheaf.stalk N.point) R] :
    FinitePresentationIsoOverOpen (closedPointComplementι X hx) ⥤
      @FinitePresentationIsoOverOpen S _ _ (henselizationPuncturedι X x N hN R) (Henselization.isOpenImmersion_puncturedι R (henselizationOver X x N hN R).hom) :=
  ObjectProperty.lift
    (@finitePresentationIsoOverOpenProperty S _ _ (henselizationPuncturedι X x N hN R) (Henselization.isOpenImmersion_puncturedι R (henselizationOver X x N hN R).hom))
    (FinitePresentationIsoOverOpen.inclusion (closedPointComplementι X hx) ⋙
      overPullback (fromHenselization X x N hN R))
    (fun Y ↦ puncturedHenselizationBaseChange_mem X hx N hN R Y)

/-- The structure morphism of a `puncturedHenselizationBaseChange` object is the
second projection of the fibre product along `fromHenselization`. -/
theorem puncturedHenselizationBaseChange_obj_hom {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] {x : Points X}
    (hx : x ∈ closedPoints (Points X))
    [QuasiCompact (closedPointComplementι X hx)]
    (N : EtaleNeighborhood X x)
    (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {x} = {N.point} ∧ N.IsElementary)
    (R : Type u) [CommRing R] [Algebra (N.scheme.presheaf.stalk N.point) R]
    [IsHenselizationOf (N.scheme.presheaf.stalk N.point) R]
    (Y : FinitePresentationIsoOverOpen (closedPointComplementι X hx)) :
    ((puncturedHenselizationBaseChange X hx N hN R).obj Y).obj.hom =
      overPullbackSnd (fromHenselization X x N hN R) Y.obj :=
  sorry

/-- Base change from a decent algebraic space to the spectrum of a henselization at
a closed point with quasi-compact complement is an equivalence on finite-presentation
morphisms that are isomorphisms over the complementary opens. -/
theorem puncturedHenselizationBaseChange_isEquivalence {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] {x : Points X}
    (hx : x ∈ closedPoints (Points X))
    [QuasiCompact (closedPointComplementι X hx)]
    (N : EtaleNeighborhood X x)
    (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {x} = {N.point} ∧ N.IsElementary)
    (R : Type u) [CommRing R] [Algebra (N.scheme.presheaf.stalk N.point) R]
    [IsHenselizationOf (N.scheme.presheaf.stalk N.point) R] :
    (puncturedHenselizationBaseChange X hx N hN R).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicSpace
