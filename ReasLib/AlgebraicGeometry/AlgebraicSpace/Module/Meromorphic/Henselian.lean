/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSheafSpace
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Henselization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Spectrum
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MeromorphicFunction.Pullback.Criteria
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.RegularPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Prime


/-! # Henselian presentations of meromorphic sections -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory PresheafOfModules
open scoped nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]

namespace MeromorphicSection

/-- Regularity of the pulled germ for a supplied affine elementary neighbourhood and henselization. -/
def IsRegularAtWith {L : X.Modules} (s : meromorphicSections X L) (x : Points X) (N : EtaleNeighborhood X x)
    (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {x} = {N.point} ∧ N.IsElementary)
    (R : Type u) [CommRing R] [Algebra (N.scheme.presheaf.stalk N.point) R]
    [IsHenselizationOf (N.scheme.presheaf.stalk N.point) R] : Prop :=
  let Y := henselizationSpace X x N hN R
  let Lx := (Modules.pullback (fromHenselization X x N hN R)).obj L
  let U := op (smallEtaleSite.id (henselizationOver X x N hN R))
  ∃ t : (Modules.liftModule Lx).val.obj U,
    (CategoryTheory.toSheafify (smallEtaleTopology Y)
        (meromorphicSectionPresheaf Y Lx).presheaf).app U (LocalizedModule.mk t 1) =
      sections.eval (@MeromorphicConstruction.Pullback.pullback S _ X (fromHenselization X x N hN R)
        (@instPullbacksMeromorphicFunctionsDefined_of_flat S _ X _
          (@Henselization.flat_fromNeighborhood S X N.toOver N.hom N.toSite.prop N.point R _ _ _)) L s) U

/-- A meromorphic section is regular at a point if its pullback is regular in a
henselian presentation at that point. -/
def IsRegularAt {L : X.Modules} (s : meromorphicSections X L) (x : Points X) : Prop :=
  ∃ (N : EtaleNeighborhood X x)
      (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {x} = {N.point} ∧ N.IsElementary)
      (R : Type u) (ring : CommRing R) (alg : Algebra (N.scheme.presheaf.stalk N.point) R)
      (henselian : IsHenselizationOf (N.scheme.presheaf.stalk N.point) R),
      IsRegularAtWith s x N hN R

/-- Regularity at a point is witnessed by a supplied henselian presentation. -/
theorem isRegularAt_iff {L : X.Modules} (s : meromorphicSections X L) (x : Points X) :
    IsRegularAt s x ↔ ∃ (N : EtaleNeighborhood X x)
      (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {x} = {N.point} ∧ N.IsElementary)
      (R : Type u) (ring : CommRing R) (alg : Algebra (N.scheme.presheaf.stalk N.point) R)
      (henselian : IsHenselizationOf (N.scheme.presheaf.stalk N.point) R),
      IsRegularAtWith s x N hN R := sorry

/-- The henselian local ring identifies with the structure sections on the identity
étale chart of any supplied henselization. -/
theorem nonempty_henselianLocalRing_equiv_identitySections (x : Points X)
    (N : EtaleNeighborhood X x)
    (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {x} = {N.point} ∧ N.IsElementary)
    (R : Type u) [CommRing R] [Algebra (N.scheme.presheaf.stalk N.point) R]
    [IsHenselizationOf (N.scheme.presheaf.stalk N.point) R] :
    Nonempty (henselianLocalRing X x ≃+*
      (commStructureSheafLift (henselizationSpace X x N hN R)).obj.obj
        (op (smallEtaleSite.id (henselizationOver X x N hN R)))) := sorry

/-- A nonzerodivisor ratio presents the pulled germ relative to a spanning generator
in the supplied henselian coordinates. -/
def IsRatioOfPulledGermWith {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (Z : PrimeDivisor X)
    (f : FractionRing (henselianLocalRing X Z.genericPoint))
    (N : EtaleNeighborhood X Z.genericPoint)
    (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {Z.genericPoint} = {N.point} ∧ N.IsElementary)
    (R : Type u) [CommRing R] [Algebra (N.scheme.presheaf.stalk N.point) R]
    [IsHenselizationOf (N.scheme.presheaf.stalk N.point) R] : Prop :=
  let ξ := Z.genericPoint
  let Y := henselizationSpace X ξ N hN R
  let Lx := (Modules.pullback (fromHenselization X ξ N hN R)).obj L
  let U := op (smallEtaleSite.id (henselizationOver X ξ N hN R))
  let A := henselianLocalRing X ξ
  let Asections := (commStructureSheafLift Y).obj.obj U
  ∃ (t : (Modules.liftModule Lx).val.obj U) (a b : A)
    (hb : b ∈ nonZeroDivisors A) (e : A ≃+* Asections)
    (hreg : e b ∈ (regularStructureSections Y).obj U),
    a ∈ nonZeroDivisors A ∧ Submodule.span Asections {t} = ⊤ ∧
      f = IsLocalization.mk' (FractionRing A) a ⟨b, hb⟩ ∧
        (CategoryTheory.toSheafify (smallEtaleTopology Y)
            (meromorphicSectionPresheaf Y Lx).presheaf).app U
          (LocalizedModule.mk (e a • t) ⟨e b, hreg⟩) =
          sections.eval (@MeromorphicConstruction.Pullback.pullback S _ X (fromHenselization X ξ N hN R)
        (@instPullbacksMeromorphicFunctionsDefined_of_flat S _ X _
          (@Henselization.flat_fromNeighborhood S X N.toOver N.hom N.toSite.prop N.point R _ _ _)) L s) U


/-- A fraction presents a meromorphic germ when it does so in a henselian presentation. -/
def IsRatioOfPulledGerm {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (Z : PrimeDivisor X)
    (f : FractionRing (henselianLocalRing X Z.genericPoint)) : Prop :=
  ∃ (N : EtaleNeighborhood X Z.genericPoint)
      (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {Z.genericPoint} = {N.point} ∧ N.IsElementary)
      (R : Type u) (ring : CommRing R) (alg : Algebra (N.scheme.presheaf.stalk N.point) R)
      (henselian : IsHenselizationOf (N.scheme.presheaf.stalk N.point) R),
      IsRatioOfPulledGermWith s Z f N hN R

/-- A ratio of a pulled germ has a supplied henselian presentation. -/
theorem isRatioOfPulledGerm_iff {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (Z : PrimeDivisor X)
    (f : FractionRing (henselianLocalRing X Z.genericPoint)) :
    IsRatioOfPulledGerm s Z f ↔ ∃ (N : EtaleNeighborhood X Z.genericPoint)
      (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {Z.genericPoint} = {N.point} ∧ N.IsElementary)
      (R : Type u) (ring : CommRing R) (alg : Algebra (N.scheme.presheaf.stalk N.point) R)
      (henselian : IsHenselizationOf (N.scheme.presheaf.stalk N.point) R),
      IsRatioOfPulledGermWith s Z f N hN R := sorry

/-- The ratio `s / s_ξ` in `Q(O_{X,ξ}^h)`, obtained by choice among fractions
presenting the pulled germ relative to a generator of `c_ξ^* L`. Downstream
users should rely on `henselianFraction_spec` rather than inspect the witness. -/
def henselianFraction {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (Z : PrimeDivisor X) : FractionRing (henselianLocalRing X Z.genericPoint) :=
  let _ := hs
  Classical.epsilon fun f : FractionRing (henselianLocalRing X Z.genericPoint) ↦
    IsRatioOfPulledGerm s Z f

/-- The constructed henselian fraction is a ratio presenting the pulled germ. -/
theorem henselianFraction_spec [IsLocallyNoetherian X] [IsIntegral X]
    {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (Z : PrimeDivisor X) :
    IsRatioOfPulledGerm s Z (henselianFraction s hs Z) := sorry

end MeromorphicSection

end AlgebraicGeometry.AlgebraicSpace
