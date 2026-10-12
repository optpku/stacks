/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.Relative
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise.Restriction
import ReasLib.Algebra.Homology.CochainComplex.Truncation.Module
import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution.Flat
import ReasLib.Algebra.Homology.DerivedCategory.ProjectiveModel
import ReasLib.Algebra.Homology.DerivedCategory.Truncation
import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.FlatCokernel.Relative
import Mathlib.Tactic.CrossRefAttribute

/-!
# Models for relative finite Tor dimension

This leaf owns the representative theorem for a derived module of finite Tor dimension over a
flat algebra.  The predicate and its ring-map restriction remain in `TorAmplitude.Relative`;
the model construction is downstream because it uses bounded-complex and flat-cokernel APIs.
@stack 0E1U
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.DerivedCategory

variable {R A : Type u} [CommRing R] [CommRing A]
variable {K : DerivedCategory (ModuleCat A)}

/-- Lemma 15.85.6 (Stacks `0E1U`): a bounded-above relatively flat representative can be cut at a lower Tor bound to produce a
bounded relatively flat representative of the same derived object. -/
@[stacks 0E1U "bounded relatively flat model from a chosen upper model"]
theorem HasTorAmplitudeGEAlong.truncGE_model
    {σ : R →+* A} {a : ℤ} (hTor : K.HasTorAmplitudeGEAlong σ a)
    (E : CochainComplex (ModuleCat A) ℤ)
    (e : DerivedCategory.Q.obj E ≅ K)
    (hE : CochainComplex.minus (ModuleCat A) E)
    (hEflat : E.IsTermwiseFlatAlong σ) :
    ∃ eF : DerivedCategory.Q.obj (E.truncGE a) ≅ K,
      CochainComplex.bounded (ModuleCat A) (E.truncGE a) ∧
        (E.truncGE a).IsTermwiseFlatAlong σ := sorry
/- Proof strategy: transport `hTor` across `e`, use the relative flat-cokernel theorem at the
cutoff degree, and combine the smart-truncation quasi-isomorphism with bounded-above support to
obtain the displayed bounded termwise-flat model. -/

/-- Lemma 15.85.6 (Stacks `0E1U`): finite Tor dimension along a flat ring map admits a bounded complex model whose
terms are flat after restriction along that map. -/
@[stacks 0E1U "bounded flat model along a flat ring map"]
theorem HasFiniteTorDimensionAlong.exists_flat_model
    {σ : R →+* A} (hK : K.HasFiniteTorDimensionAlong σ) (hσ : σ.Flat) :
    ∃ (F : CochainComplex (ModuleCat A) ℤ)
      (e : DerivedCategory.Q.obj F ≅ K),
      CochainComplex.bounded (ModuleCat A) F ∧ F.IsTermwiseFlatAlong σ := sorry
/- Proof strategy: unpack a Tor-amplitude interval, obtain an `A`-linear projective-minus model
from its upper bound, restrict termwise flatness along `σ` using `IsTermwiseFlat.along`, and cut
the model at the lower bound with `HasTorAmplitudeGEAlong.truncGE_model`. -/

/-- Lemma 15.85.6 (Stacks `0E1U`): over a flat algebra, finite Tor dimension over the base admits a bounded `A`-complex model
whose terms are flat over the base, together with an explicit comparison isomorphism. -/
@[stacks 0E1U "bounded relatively flat model"]
theorem HasFiniteTorDimensionOver.exists_flat_model
    [Algebra R A] [Module.Flat R A]
    (hK : K.HasFiniteTorDimensionOver R) :
    ∃ (F : CochainComplex (ModuleCat A) ℤ)
      (e : DerivedCategory.Q.obj F ≅ K),
      CochainComplex.bounded (ModuleCat A) F ∧ F.IsTermwiseFlatOver R := sorry
/- Proof strategy: apply `HasFiniteTorDimensionAlong.exists_flat_model` to `algebraMap R A`,
using `RingHom.flat_algebraMap_iff` to supply flatness of the ring map. -/

end CategoryTheory.DerivedCategory

end
