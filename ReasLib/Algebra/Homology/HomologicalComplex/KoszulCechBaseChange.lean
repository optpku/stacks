/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.Algebra.Homology.HomotopyCategory.QuasiIso
public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Alternating
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.RingTheory.Sequence.Koszul.Family
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat base change for Koszul and extended Cech complexes

When a flat ring map is an isomorphism modulo a finitely generated ideal, scalar extension is a
quasi-isomorphism on the Koszul and extended alternating Cech complexes supported on that ideal.

@stack 091M
-/

@[expose] public section

noncomputable section

open CategoryTheory ComplexShape

universe u

namespace KoszulComplex

/-- Lemma 15.90.4 (1), Stacks `091M`: under a flat ring map which is an isomorphism modulo a
finitely generated ideal `I`, the scalar-extension unit on a finite-family Koszul complex is a
quasi-isomorphism when the family and `I` have the same zero locus. -/
@[stacks 091M "(1), flat base change for a Koszul complex"]
theorem baseChangeUnit_quasiIso_of_quotientMap_bijective
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (I : Ideal R) {r : ℕ} (f : Fin r → R) (hI : I.FG)
    (hquotient :
      Function.Bijective
        (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (hzeroLocus : PrimeSpectrum.zeroLocus (Ideal.span (Set.range f) : Set R) =
      PrimeSpectrum.zeroLocus (I : Set R)) :
    QuasiIso
      ((((Functor.mapHomologicalComplexIdIso (ModuleCat R) (down ℕ)).inv ≫
          NatTrans.mapHomologicalComplex
            (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).unit (down ℕ)).app
        (family f))) := sorry

end KoszulComplex

namespace LocalizedModule.Away.Cech.Alternating

/-- Lemma 15.90.4 (2), Stacks `091M`: under a flat ring map which is an isomorphism modulo a
finitely generated ideal `I`, the scalar-extension unit on the extended alternating Cech complex
is a quasi-isomorphism when its defining family and `I` have the same zero locus. -/
@[stacks 091M "(2), flat base change for an extended alternating Cech complex"]
theorem extended_baseChangeUnit_quasiIso_of_quotientMap_bijective
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (I : Ideal R) {r : ℕ} (f : Fin r → R) (hI : I.FG)
    (hquotient :
      Function.Bijective
        (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (hzeroLocus : PrimeSpectrum.zeroLocus (Ideal.span (Set.range f) : Set R) =
      PrimeSpectrum.zeroLocus (I : Set R)) :
    QuasiIso
      ((((Functor.mapHomologicalComplexIdIso (ModuleCat R) (up ℕ)).inv ≫
          NatTrans.mapHomologicalComplex
            (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).unit (up ℕ)).app
        (extended f R))) := sorry

end LocalizedModule.Away.Cech.Alternating
