/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.LocalizedChern.Compactification.BaseChange

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/- Lemma 42.49.2 (1): the localized Newton class
commutes with locally finite-type base change of the compactification and complex. -/
@[stacks 0GUI] #check (AlgebraicGeometry.LocalizedChern.newtonClassAtZero_eq_restrict :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X X' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    {Z Z' W W' T T' : Scheme.{u}}
    (i : Z ⟶ X.left) (i' : Z' ⟶ X'.left)
    [IsClosedImmersion i] [IsClosedImmersion i']
    (g : X' ⟶ X) [LocallyOfFiniteType g.left]
    (gZ : Over.mk (i' ≫ X'.hom) ⟶ Over.mk (i ≫ X.hom))
    (squareZ : IsPullback gZ.left
      (Over.homMk i' : Over.mk (i' ≫ X'.hom) ⟶ X').left
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X).left g.left)
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (b' : W' ⟶ ProjectiveLineFamily.space X') [IsProper b']
    [IsIso (b' ∣_ BivariantClass.GysinAtInfinity.affinePart X')]
    (h : BivariantClass.GysinAtInfinity.compactification X' b' ⟶
      BivariantClass.GysinAtInfinity.compactification X b)
    (hb : IsPullback h.left b' b (ProjectiveLineFamily.map g))
    (gInf : BivariantClass.GysinAtInfinity.infinityFiber X' b' ⟶
      BivariantClass.GysinAtInfinity.infinityFiber X b)
    (hgInf : gInf ≫ BivariantClass.GysinAtInfinity.infinityInclusion X b =
      BivariantClass.GysinAtInfinity.infinityInclusion X' b' ≫ h)
    (squareInf : IsPullback gInf.left
      (BivariantClass.GysinAtInfinity.infinityToX X' b').left
      (BivariantClass.GysinAtInfinity.infinityToX X b).left g.left)
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    (t' : T' ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X' b').left)
    [IsClosedImmersion t] [IsClosedImmersion t']
    (gT : Over.mk (t' ≫ (BivariantClass.GysinAtInfinity.infinityFiber X' b').hom) ⟶
      Over.mk (t ≫ (BivariantClass.GysinAtInfinity.infinityFiber X b).hom))
    (squareT : IsPullback gT.left t' t gInf.left)
    (Q : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect Q)
    (defined : ∃ (Y : Scheme.{u}) (f : Y ⟶ W), IsEnvelope f ∧
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
        ((RingedSpace.modulePullbackDerived f.toShHom).obj Q))
    (classes : ChernClass.Theory δ
      (BivariantClass.GysinAtInfinity.compactification X b).hom)
    (containsComplement :
      (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
        (Set.range i.base)ᶜ ⊆ Set.range t.base)
    (p : ℕ)
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q))
    (output : BivariantClass δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))
    (output' : BivariantClass δ
      (Over.homMk i' : Over.mk (i' ≫ X'.hom) ⟶ X') (p : ℤ))
    (houtput : IsCompactificationLocalization δ i b t (p : ℤ)
      (EnvelopeCaps.derivedClass δ classes Q perfect defined false p) output)
    (houtput' : IsCompactificationLocalization δ i' b' t' (p : ℤ)
      (EnvelopeCaps.derivedClass δ
        (classes.reanchor (BivariantClass.GysinAtInfinity.compactification X' b'))
        ((RingedSpace.modulePullbackDerived h.left.toShHom).obj Q)
        (RingedSpace.modulePullbackDerived_isPerfect h.left.toShHom Q perfect)
        (EnvelopeCaps.defined_pullback h.left Q defined) false p) output'),
    output' = BivariantClass.restrict δ gZ
      (Over.homMk i' : Over.mk (i' ≫ X'.hom) ⟶ X') g squareZ (p : ℤ) output)

/- Lemma 42.49.2 (2): the localized Chern class
commutes with locally finite-type base change of the compactification and complex. -/
@[stacks 0GUI] #check (AlgebraicGeometry.LocalizedChern.chernClassAtZero_eq_restrict :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X X' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    {Z Z' W W' T T' : Scheme.{u}}
    (i : Z ⟶ X.left) (i' : Z' ⟶ X'.left)
    [IsClosedImmersion i] [IsClosedImmersion i']
    (g : X' ⟶ X) [LocallyOfFiniteType g.left]
    (gZ : Over.mk (i' ≫ X'.hom) ⟶ Over.mk (i ≫ X.hom))
    (squareZ : IsPullback gZ.left
      (Over.homMk i' : Over.mk (i' ≫ X'.hom) ⟶ X').left
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X).left g.left)
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (b' : W' ⟶ ProjectiveLineFamily.space X') [IsProper b']
    [IsIso (b' ∣_ BivariantClass.GysinAtInfinity.affinePart X')]
    (h : BivariantClass.GysinAtInfinity.compactification X' b' ⟶
      BivariantClass.GysinAtInfinity.compactification X b)
    (hb : IsPullback h.left b' b (ProjectiveLineFamily.map g))
    (gInf : BivariantClass.GysinAtInfinity.infinityFiber X' b' ⟶
      BivariantClass.GysinAtInfinity.infinityFiber X b)
    (hgInf : gInf ≫ BivariantClass.GysinAtInfinity.infinityInclusion X b =
      BivariantClass.GysinAtInfinity.infinityInclusion X' b' ≫ h)
    (squareInf : IsPullback gInf.left
      (BivariantClass.GysinAtInfinity.infinityToX X' b').left
      (BivariantClass.GysinAtInfinity.infinityToX X b).left g.left)
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    (t' : T' ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X' b').left)
    [IsClosedImmersion t] [IsClosedImmersion t']
    (gT : Over.mk (t' ≫ (BivariantClass.GysinAtInfinity.infinityFiber X' b').hom) ⟶
      Over.mk (t ≫ (BivariantClass.GysinAtInfinity.infinityFiber X b).hom))
    (squareT : IsPullback gT.left t' t gInf.left)
    (Q : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect Q)
    (defined : ∃ (Y : Scheme.{u}) (f : Y ⟶ W), IsEnvelope f ∧
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
        ((RingedSpace.modulePullbackDerived f.toShHom).obj Q))
    (classes : ChernClass.Theory δ
      (BivariantClass.GysinAtInfinity.compactification X b).hom)
    (containsComplement :
      (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
        (Set.range i.base)ᶜ ⊆ Set.range t.base)
    (p : ℕ)
    (restrictionRank : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q)
      0 p)
    (output : BivariantClass δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))
    (output' : BivariantClass δ
      (Over.homMk i' : Over.mk (i' ≫ X'.hom) ⟶ X') (p : ℤ))
    (houtput : IsCompactificationLocalization δ i b t (p : ℤ)
      (EnvelopeCaps.derivedClass δ classes Q perfect defined true p) output)
    (houtput' : IsCompactificationLocalization δ i' b' t' (p : ℤ)
      (EnvelopeCaps.derivedClass δ
        (classes.reanchor (BivariantClass.GysinAtInfinity.compactification X' b'))
        ((RingedSpace.modulePullbackDerived h.left.toShHom).obj Q)
        (RingedSpace.modulePullbackDerived_isPerfect h.left.toShHom Q perfect)
        (EnvelopeCaps.defined_pullback h.left Q defined) true p) output'),
    output' = BivariantClass.restrict δ gZ
      (Over.homMk i' : Over.mk (i' ≫ X'.hom) ⟶ X') g squareZ (p : ℤ) output)

end AlgebraicGeometry.LocalizedChern
