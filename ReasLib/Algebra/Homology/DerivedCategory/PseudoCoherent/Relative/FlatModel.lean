/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FinitePresentation
import ReasLib.Algebra.Category.ModuleCat.FlatResolution
import ReasLib.Algebra.Homology.CochainComplex.Bounded.Map
import ReasLib.Algebra.Homology.CochainComplex.Cokernel.FinitePresentation
import ReasLib.Algebra.Homology.CochainComplex.Truncation.Module
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Perfect
import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.FlatFinitePresentation
import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Model
import ReasLib.Algebra.Homology.DerivedCategory.Truncation
import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.FlatCokernel.Relative
import ReasLib.Algebra.Homology.HomologicalComplex.Termwise.FiniteProjective
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise.FinitePresentation
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise.Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finitely presented relative flat models

@stack 0DHV
@stack 0E1U

Over a flat algebra, pseudo-coherence and finite Tor dimension strengthen the bounded
relative-flat model to one whose terms are finitely presented over the target algebra.  Finite
presentation of the algebra map enters only in the converse criterion.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.DerivedCategory.HasTorAmplitudeGEAlong

variable {R A : Type u} [CommRing R] [CommRing A]
variable {K : DerivedCategory (ModuleCat A)}

/-- Lemma 15.85.6 (Stacks `0E1U`): a chosen bounded-above relatively flat model with finitely presented terms can be cut at a
lower Tor bound to produce a bounded relatively flat finitely presented model. -/
@[stacks 0E1U "bounded finite-presentation model from a chosen upper model"]
theorem truncGE_model_finitePresentation
    {σ : R →+* A} {a : ℤ} (hTor : K.HasTorAmplitudeGEAlong σ a)
    (E : CochainComplex (ModuleCat A) ℤ)
    (e : DerivedCategory.Q.obj E ≅ K)
    (hE : CochainComplex.minus (ModuleCat A) E)
    (hEflat : E.IsTermwiseFlatAlong σ)
    (hEfp : E.IsTermwiseFinitePresentation) :
    ∃ eF : DerivedCategory.Q.obj (E.truncGE a) ≅ K,
      CochainComplex.bounded (ModuleCat A) (E.truncGE a) ∧
        (E.truncGE a).IsTermwiseFlatAlong σ ∧
          (E.truncGE a).IsTermwiseFinitePresentation := sorry
/- Proof strategy: use the lower Tor bound to identify the good truncation with `K` through
`DerivedCategory.Q.truncGEIso`; boundedness follows from the bounded-above hypothesis, while
`CochainComplex.IsTermwiseFlatAlong.truncGE_of_opcycles` and
`CochainComplex.IsTermwiseFinitePresentation.truncGE_of_opcycles` handle the new boundary term via
the flat-cokernel and finite-presentation opcycles bridges. -/

end CategoryTheory.DerivedCategory.HasTorAmplitudeGEAlong

namespace CategoryTheory.DerivedCategory.IsPseudoCoherent

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {K : DerivedCategory (ModuleCat A)}

/-- Lemma 15.85.4 (Stacks `0DHV`); Lemma 15.85.6 (Stacks `0E1U`): a pseudo-coherent object with a lower relative Tor-amplitude bound admits a bounded model whose
terms are flat over the base and finitely presented over the target. -/
@[stacks 0DHV "flat finite-presentation model from a lower Tor bound",
  stacks 0E1U "lower-bound model producer"]
theorem exists_flat_finitePresentation_model [Module.Flat R A]
    (hK : K.IsPseudoCoherent) {a : ℤ}
    (hTor : K.HasTorAmplitudeGEOver R a) :
    ∃ (F : CochainComplex (ModuleCat A) ℤ)
      (e : DerivedCategory.Q.obj F ≅ K),
      CochainComplex.bounded (ModuleCat A) F ∧
        F.IsTermwiseFlatOver R ∧ F.IsTermwiseFinitePresentation := sorry
/- Proof strategy: choose `DerivedCategory.IsPseudoCoherent.exists_finiteFree_model`, restrict its
finite-free terms along `R → A` using flatness of `A`, and apply
`HasTorAmplitudeGEAlong.truncGE_model_finitePresentation` at the supplied lower Tor bound. -/

end CategoryTheory.DerivedCategory.IsPseudoCoherent

namespace CategoryTheory.DerivedCategory.IsPerfectOver

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {K : DerivedCategory (ModuleCat A)}

/-- Lemma 15.85.6 (Stacks `0E1U`): the forward direction of Lemma 15.85.4 (Stacks `0DHV`), used in Lemma 15.85.6
(Stacks `0E1U`): over a flat algebra, a pseudo-coherent object of finite Tor dimension over the
base has a bounded model that is termwise flat over the base and termwise finitely presented over
the algebra.  Finite presentation of `R → A` is not needed in this direction. -/
@[stacks 0E1U "finitely presented bounded relatively flat model"]
theorem exists_flat_finitePresentation_model [Module.Flat R A]
    (hK : IsPerfectOver R K) :
    ∃ (F : CochainComplex (ModuleCat A) ℤ)
      (e : DerivedCategory.Q.obj F ≅ K),
      CochainComplex.bounded (ModuleCat A) F ∧
        F.IsTermwiseFlatOver R ∧ F.IsTermwiseFinitePresentation := sorry
/- Proof strategy: obtain a bounded-above finite-free model from
`DerivedCategory.IsPseudoCoherent.exists_finiteFree_model`, pass its finite-free terms through
`HomologicalComplex.IsTermwiseFlat.over`, choose a lower Tor bound, and apply
`CochainComplex.bounded_truncGE` together with
`CochainComplex.IsTermwiseFlatOver.truncGE_of_opcycles` and
`CochainComplex.IsTermwiseFinitePresentation.truncGE_of_opcycles`.  The boundary flatness is the
canonical `FlatCokernel.ofTorAmplitudeGEOver` conclusion, while finite presentation of the
opcycles comes from `CochainComplex.IsTermwiseFinitePresentation.opcycles`; the derived comparison
is transported through `DerivedCategory.Q.truncGEIso`.  These named interfaces are packaged by
`HasTorAmplitudeGEAlong.truncGE_model_finitePresentation`, keeping the cutoff
construction independent of this producer.  No Chapter declaration is imported by this owner. -/

/- The converse is kept at the same explicit model boundary.  This gives downstream users a
  witness-oriented entry point without forcing them through a chapter-local bundled complex. -/

/-- Lemma 15.85.4 (Stacks `0DHV`), converse: a bounded relatively flat finitely presented model
represents a relatively perfect object. -/
@[stacks 0DHV "relative-perfectness from a bounded flat finite-presentation model"]
theorem of_flat_finitePresentation_model
    [Algebra.FinitePresentation R A] [Module.Flat R A]
    (F : CochainComplex (ModuleCat A) ℤ)
    (e : DerivedCategory.Q.obj F ≅ K)
    (hF : CochainComplex.bounded (ModuleCat A) F)
    (hFflat : F.IsTermwiseFlatOver R)
    (hFfp : F.IsTermwiseFinitePresentation) :
    IsPerfectOver R K := sorry
/- Proof strategy: use `isPerfectOver_iff` to split the target into pseudo-coherence and finite Tor
dimension; establish pseudo-coherence of the bounded termwise finite-presentation model and finite
Tor dimension of its termwise `IsTermwiseFlatOver R` restriction using
`CochainComplex.bounded_map`, `ModuleCat.hasTorDimensionLE_zero_iff_flat`, and
`HasFiniteTorDimension.of_bounded_of_termwise`; then transport both parts along `e` with
`IsPerfectOver.ofIso`. -/

/-- Lemma 15.85.4 (Stacks `0DHV`): relative perfectness is equivalent to admitting a bounded
relatively flat finitely presented model. -/
@[stacks 0DHV "relative-perfect model criterion"]
theorem iff_exists_flat_finitePresentation_model
    [Algebra.FinitePresentation R A] [Module.Flat R A]
    (K : DerivedCategory (ModuleCat A)) :
    IsPerfectOver R K ↔
      ∃ (F : CochainComplex (ModuleCat A) ℤ)
        (e : DerivedCategory.Q.obj F ≅ K),
        CochainComplex.bounded (ModuleCat A) F ∧
          F.IsTermwiseFlatOver R ∧ F.IsTermwiseFinitePresentation := sorry
/- Proof strategy: the forward implication is `exists_flat_finitePresentation_model`; unpack a
 witness for the reverse implication and apply `of_flat_finitePresentation_model`. -/

end CategoryTheory.DerivedCategory.IsPerfectOver
