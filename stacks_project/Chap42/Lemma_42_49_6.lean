/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.LocalizedChern.Compactification.Newton

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

#check (AlgebraicGeometry.LocalizedChern.newtonClassAtZero_one :
  ∀
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W T : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (Q : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect Q)
    (defined : ∃ (Y : Scheme.{u}) (f : Y ⟶ W), IsEnvelope f ∧
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
        ((RingedSpace.modulePullbackDerived f.toShHom).obj Q))
    (classes : ChernClass.Theory δ
      (BivariantClass.GysinAtInfinity.compactification X b).hom)
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t]
    (containsComplement :
      (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
          (Set.range i.base)ᶜ ⊆ Set.range t.base)
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q))
    (P c : (p : ℕ) → BivariantClass δ
      (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))
    (P_spec : ∀ p : ℕ, 0 < p →
      IsCompactificationLocalization δ i b t (p : ℤ)
        (EnvelopeCaps.derivedClass δ classes Q perfect defined false p) (P p))
    (c_spec : ∀ p : ℕ, 0 < p →
      IsCompactificationLocalization δ i b t (p : ℤ)
        (EnvelopeCaps.derivedClass δ classes Q perfect defined true p) (c p)),
    P 1 =
      c 1)

#check (AlgebraicGeometry.LocalizedChern.newtonClassAtZero_two :
  ∀
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W T : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (Q : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect Q)
    (defined : ∃ (Y : Scheme.{u}) (f : Y ⟶ W), IsEnvelope f ∧
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
        ((RingedSpace.modulePullbackDerived f.toShHom).obj Q))
    (classes : ChernClass.Theory δ
      (BivariantClass.GysinAtInfinity.compactification X b).hom)
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t]
    (containsComplement :
      (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
          (Set.range i.base)ᶜ ⊆ Set.range t.base)
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q))
    (P c : (p : ℕ) → BivariantClass δ
      (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))
    (P_spec : ∀ p : ℕ, 0 < p →
      IsCompactificationLocalization δ i b t (p : ℤ)
        (EnvelopeCaps.derivedClass δ classes Q perfect defined false p) (P p))
    (c_spec : ∀ p : ℕ, 0 < p →
      IsCompactificationLocalization δ i b t (p : ℤ)
        (EnvelopeCaps.derivedClass δ classes Q perfect defined true p) (c p)),
    P 2 =
      (BivariantClass.pointwiseAdd δ
        (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 2
        (BivariantClass.Cutoff.relativeMul δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 1 1
          (c 1)
          (c 1))
        (BivariantClass.pointwiseNeg δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 2
          (BivariantClass.pointwiseZsmul δ
            (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 2
            (c 2)
            2))))

#check (AlgebraicGeometry.LocalizedChern.newtonClassAtZero_three :
  ∀
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W T : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (Q : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect Q)
    (defined : ∃ (Y : Scheme.{u}) (f : Y ⟶ W), IsEnvelope f ∧
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
        ((RingedSpace.modulePullbackDerived f.toShHom).obj Q))
    (classes : ChernClass.Theory δ
      (BivariantClass.GysinAtInfinity.compactification X b).hom)
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t]
    (containsComplement :
      (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
          (Set.range i.base)ᶜ ⊆ Set.range t.base)
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q))
    (P c : (p : ℕ) → BivariantClass δ
      (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))
    (P_spec : ∀ p : ℕ, 0 < p →
      IsCompactificationLocalization δ i b t (p : ℤ)
        (EnvelopeCaps.derivedClass δ classes Q perfect defined false p) (P p))
    (c_spec : ∀ p : ℕ, 0 < p →
      IsCompactificationLocalization δ i b t (p : ℤ)
        (EnvelopeCaps.derivedClass δ classes Q perfect defined true p) (c p)),
    P 3 =
      (BivariantClass.pointwiseAdd δ
        (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 3
        (BivariantClass.pointwiseAdd δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 3
          (BivariantClass.Cutoff.relativeMul δ
            (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 2 1
            (BivariantClass.Cutoff.relativeMul δ
              (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 1 1
              (c 1)
              (c 1))
            (c 1))
          (BivariantClass.pointwiseNeg δ
            (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 3
            (BivariantClass.pointwiseZsmul δ
              (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 3
              (BivariantClass.Cutoff.relativeMul δ
                (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 1 2
                (c 1)
                (c 2))
              3)))
        (BivariantClass.pointwiseZsmul δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 3
          (c 3)
          3)))

#check (AlgebraicGeometry.LocalizedChern.newtonClassAtZero_four :
  ∀
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W T : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (Q : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect Q)
    (defined : ∃ (Y : Scheme.{u}) (f : Y ⟶ W), IsEnvelope f ∧
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
        ((RingedSpace.modulePullbackDerived f.toShHom).obj Q))
    (classes : ChernClass.Theory δ
      (BivariantClass.GysinAtInfinity.compactification X b).hom)
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t]
    (containsComplement :
      (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
          (Set.range i.base)ᶜ ⊆ Set.range t.base)
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q))
    (P c : (p : ℕ) → BivariantClass δ
      (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))
    (P_spec : ∀ p : ℕ, 0 < p →
      IsCompactificationLocalization δ i b t (p : ℤ)
        (EnvelopeCaps.derivedClass δ classes Q perfect defined false p) (P p))
    (c_spec : ∀ p : ℕ, 0 < p →
      IsCompactificationLocalization δ i b t (p : ℤ)
        (EnvelopeCaps.derivedClass δ classes Q perfect defined true p) (c p)),
    P 4 =
      (BivariantClass.pointwiseAdd δ
        (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 4
        (BivariantClass.pointwiseAdd δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 4
          (BivariantClass.pointwiseAdd δ
            (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 4
            (BivariantClass.pointwiseAdd δ
              (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 4
              (BivariantClass.Cutoff.relativeMul δ
                (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 3 1
                (BivariantClass.Cutoff.relativeMul δ
                  (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 2 1
                  (BivariantClass.Cutoff.relativeMul δ
                    (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 1 1
                    (c 1)
                    (c 1))
                  (c 1))
                (c 1))
              (BivariantClass.pointwiseNeg δ
                (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 4
                (BivariantClass.pointwiseZsmul δ
                  (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 4
                  (BivariantClass.Cutoff.relativeMul δ
                    (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 2 2
                    (BivariantClass.Cutoff.relativeMul δ
                      (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 1 1
                      (c 1)
                      (c 1))
                    (c 2))
                  4)))
            (BivariantClass.pointwiseZsmul δ
              (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 4
              (BivariantClass.Cutoff.relativeMul δ
                (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 1 3
                (c 1)
                (c 3))
              4))
          (BivariantClass.pointwiseZsmul δ
            (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 4
            (BivariantClass.Cutoff.relativeMul δ
              (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 2 2
              (c 2)
              (c 2))
            2))
        (BivariantClass.pointwiseNeg δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 4
          (BivariantClass.pointwiseZsmul δ
            (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 4
            (c 4)
            4))))

/- Lemma 42.49.6. The localized Newton identities, in all positive degrees. -/
@[stacks 0FAX]
#check (AlgebraicGeometry.LocalizedChern.newtonClassAtZero_succ :
  ∀
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W T : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (Q : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect Q)
    (defined : ∃ (Y : Scheme.{u}) (f : Y ⟶ W), IsEnvelope f ∧
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
        ((RingedSpace.modulePullbackDerived f.toShHom).obj Q))
    (classes : ChernClass.Theory δ
      (BivariantClass.GysinAtInfinity.compactification X b).hom)
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t]
    (containsComplement :
      (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
          (Set.range i.base)ᶜ ⊆ Set.range t.base)
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q))
    (P c : (p : ℕ) → BivariantClass δ
      (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))
    (P_spec : ∀ p : ℕ, 0 < p →
      IsCompactificationLocalization δ i b t (p : ℤ)
        (EnvelopeCaps.derivedClass δ classes Q perfect defined false p) (P p))
    (c_spec : ∀ p : ℕ, 0 < p →
      IsCompactificationLocalization δ i b t (p : ℤ)
        (EnvelopeCaps.derivedClass δ classes Q perfect defined true p) (c p))
    (n : ℕ),
    P (n + 1) =
      (BivariantClass.pointwiseAdd δ
        (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) ((n + 1 : ℕ) : ℤ)
        (BivariantClass.pointwiseSum δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) ((n + 1 : ℕ) : ℤ)
          (Finset.univ : Finset (Finset.range n))
          (fun j ↦
            (BivariantClass.pointwiseZsmul δ
              (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) ((n + 1 : ℕ) : ℤ)
              (BivariantClass.Nonnegative.castGrading δ
                (show ((j.1 + 1 : ℕ) : ℤ) + ((n - j.1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) by
                  have hj : j.1 < n := Finset.mem_range.mp j.2
                  omega)
                (BivariantClass.Cutoff.relativeMul δ
                  (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) ((j.1 + 1 : ℕ) : ℤ) ((n - j.1 : ℕ) : ℤ)
                  (c (j.1 + 1))
                  (P (n - j.1))))
              ((-1 : ℤ) ^ j.1))))
        (BivariantClass.pointwiseZsmul δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) ((n + 1 : ℕ) : ℤ)
          (c (n + 1))
          ((-1 : ℤ) ^ n * (n + 1 : ℕ)))))

end AlgebraicGeometry.LocalizedChern
