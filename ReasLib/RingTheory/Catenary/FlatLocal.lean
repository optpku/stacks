/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Catenary.Basic
public import ReasLib.RingTheory.RingHom.FaithfullyFlat.Noetherian
public import ReasLib.Topology.KrullDimension.Equidimensional

@[expose] public section

/-!
# Catenarity along flat local maps

This leaf owns the source and quotient consequences of a flat local ring
homomorphism. The map is kept as an explicit `RingHom`, so the API applies to
algebra maps and to independently bundled ring maps without rebuilding local
algebra instances in downstream proofs.

@stack 033E
@stack 0AW4
-/

universe u v

open TopologicalSpace

namespace RingHom.Flat.Local

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B]

/-- Noetherianity descends from the target along a flat local ring homomorphism.
This is the flat-local specialization of faithful-flat Noetherian descent. -/
@[stacks 033E "Noetherian descent along a flat local map"]
theorem isNoetherianRing (f : A →+* B) [IsLocalHom f] (hf : f.Flat)
    [IsNoetherianRing B] :
    IsNoetherianRing A := sorry
-- Proof strategy: a flat local ring homomorphism is faithfully flat; apply canonical
-- Noetherian descent along faithfully flat maps.

variable [IsNoetherianRing B] [IsCatenaryRing B]
variable [EquidimensionalSpace (PrimeSpectrum B)]

/-- Lemma 15.110.3 (1) (current Stacks numbering: Lemma 15.111.3, tag
`0AW4`): every prime quotient of the source has an equidimensional target
quotient under a flat local map with catenary equidimensional target. -/
@[stacks 0AW4 "Lemma 15.110.3 (1), equidimensional quotient"]
theorem equidimensional_quotient (f : A →+* B) [IsLocalHom f] (hf : f.Flat)
    (p : PrimeSpectrum A) :
    EquidimensionalSpace
      (PrimeSpectrum (B ⧸ Ideal.map f p.asIdeal)) := sorry
-- Proof strategy: use flat going-down and the catenary dimension formula to compare maximal
-- chains in the fiber over `p`; equidimensionality of `PrimeSpectrum B` makes their lengths
-- independent of the chosen maximal prime.

/-- Lemma 15.110.3 (2) (current Stacks numbering: Lemma 15.111.3, tag
`0AW4`): a flat local map with catenary equidimensional Noetherian target
forces the source spectrum to be catenary. -/
@[stacks 0AW4 "Lemma 15.110.3 (2), source catenarity"]
theorem catenarySpace (f : A →+* B) [IsLocalHom f] (hf : f.Flat) :
    CatenarySpace (PrimeSpectrum A) := sorry
-- Proof strategy: lift comparable prime chains along the faithfully flat local map and use
-- catenarity of `B` together with `equidimensional_quotient` to show all saturated chains in
-- the source interval have the same finite length.

/-- Lemma 15.110.3 (3) (current Stacks numbering: Lemma 15.111.3, tag
`0AW4`): under the same hypotheses, the source spectrum is equidimensional. -/
@[stacks 0AW4 "Lemma 15.110.3 (3), source equidimensionality"]
theorem equidimensionalSpace (f : A →+* B) [IsLocalHom f] (hf : f.Flat) :
    EquidimensionalSpace (PrimeSpectrum A) := sorry
-- Proof strategy: combine source catenarity from `catenarySpace` with the flat local dimension
-- formula and equidimensionality of the target to identify the dimensions of all source
-- irreducible components.

end RingHom.Flat.Local
