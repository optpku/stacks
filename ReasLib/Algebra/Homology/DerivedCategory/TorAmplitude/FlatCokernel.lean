module

public import ReasLib.Algebra.Category.ModuleCat.Flat
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.Algebra.Homology.CochainComplex.Cokernel.Opcycles
public import ReasLib.Algebra.Homology.HomologicalComplex.Flat.Cokernel
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat boundary cokernels from Tor-amplitude

The canonical homological object is `E.opcycles a`.  This leaf records the module-category
specialization of the abstract opcycles criterion and exposes the source-facing differential
cokernel only through the canonical `opcyclesIsoCokernel` comparison.

@stack 0653
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.FlatCokernel

variable {R : Type u} [CommRing R]

/-- Stacks `0653`: exactness after tensoring a termwise-flat complex makes its degree-`a` opcycles flat. -/
@[stacks 0653 "flat opcycles from tensor exactness"]
theorem ofExactAtTensorSingle
    (E : CochainComplex (ModuleCat R) ℤ) (a : ℤ)
    (hFlat : E.IsTermwiseFlat)
    (hExact : ∀ M : ModuleCat R,
      ((E.sc (a - 1)).map (tensorRight M)).Exact) :
    Module.Flat R (E.opcycles a) := sorry

/- Proof strategy: apply `HomologicalComplex.IsTermwiseFlat.isFlat_opcycles`, then transport the
categorical flatness predicate through `ModuleCat.isFlat_iff_module_flat`. -/

/-- Stacks `0653`: a bounded-above termwise-flat representative with lower Tor-amplitude bound `a` has flat
opcycles in degree `a`. -/
@[stacks 0653 "flat opcycles from a lower Tor bound"]
theorem ofTorAmplitudeGE
    (E : CochainComplex (ModuleCat R) ℤ) (a : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat R) E)
    (hFlat : E.IsTermwiseFlat)
    (hTor : HasTorAmplitudeGE R (DerivedCategory.Q.obj E) a) :
    Module.Flat R (E.opcycles a) := sorry
/- Proof strategy: use `hTor` to obtain exactness of the tensorized three-term segment below `a`,
then invoke `ofExactAtTensorSingle`.  The bounded-above hypothesis supplies the K-flat
representative comparison used to read derived tensor homology from `E`. -/

/- The opcycles conclusion is canonical at the homological-complex layer.  This companion keeps
the source-facing incoming-differential cokernel available without making downstream users repeat
the categorical flatness transport. -/

/-- Stacks `0653`: a lower Tor-amplitude bound makes the incoming differential cokernel flat. -/
@[stacks 0653 "flat differential cokernel from a lower Tor bound"]
theorem ofTorAmplitudeGE_cokernel
    (E : CochainComplex (ModuleCat R) ℤ) (a : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat R) E)
    (hFlat : E.IsTermwiseFlat)
    (hTor : HasTorAmplitudeGE R (DerivedCategory.Q.obj E) a) :
    Module.Flat R (E.differentialCokernel a) := sorry
/- Proof strategy: apply ofTorAmplitudeGE to obtain flatness of E.opcycles a, transport
categorical flatness through E.opcyclesIsoCokernel a, and convert back with
ModuleCat.isFlat_iff_module_flat. -/

/-- Lemma 15.67.2 (Stacks `0653`): a bounded-above termwise-flat complex with Tor-amplitude in
`[a, b]` has flat incoming-differential cokernel in degree `a`. -/
@[stacks 0653 "flat differential cokernel from finite Tor amplitude"]
theorem ofTorAmplitudeIn_cokernel
    (E : CochainComplex (ModuleCat R) ℤ) (a b : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat R) E)
    (hFlat : E.IsTermwiseFlat)
    (hTor : HasTorAmplitudeIn R (DerivedCategory.Q.obj E) a b) :
    Module.Flat R (E.differentialCokernel a) := sorry
/- Proof strategy: first use `HasTorAmplitudeIn.hasTorAmplitudeGE`, then invoke
`ofTorAmplitudeGE_cokernel`; equivalently, transport the canonical opcycles conclusion across
`E.opcyclesIsoCokernel a`. -/

/-- Stacks `0653`: the canonical homological conclusion is flatness of opcycles; the differential-cokernel form is
obtained through `opcyclesIsoCokernel`. -/
@[stacks 0653 "flat opcycles from finite Tor amplitude"]
theorem ofTorAmplitudeIn
    (E : CochainComplex (ModuleCat R) ℤ) (a b : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat R) E)
    (hFlat : E.IsTermwiseFlat)
    (hTor : HasTorAmplitudeIn R (DerivedCategory.Q.obj E) a b) :
    Module.Flat R (E.opcycles a) := sorry
/- Proof strategy: extract the lower bound from `hTor` and apply `ofTorAmplitudeGE`. -/

end CategoryTheory.DerivedCategory.FlatCokernel
