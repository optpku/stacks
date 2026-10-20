module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import ReasLib.Algebra.Homology.CochainComplex.Cokernel.FinitePresentation
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Model
import Mathlib.Tactic.CrossRefAttribute

/-!
# Embedding pseudo-coherent homology into a finitely presented module

This leaf owns the canonical map from a derived object to the single object on an incoming
differential cokernel.  The source theorem then chooses a bounded-above finite-free model of a
pseudo-coherent object and transports the resulting monomorphism.

The legacy helper names in `CategoryTheory` are retained because later projective-amplitude and
Tor-amplitude arguments use the same concrete cokernel-to-single map.

@stack 0G8Y
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CochainComplex.HomComplex.Cocycle

universe u

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single" => DerivedCategory.singleFunctor (ModuleCat R)

namespace DerivedCategory

/-- The canonical map `H^i(K) ⟶ M` induced by a morphism from `K` to the degree-`i` single
object on `M`. -/
@[stacks 0G8Y "homology map induced by a morphism to a single object"]
abbrev homologyToSingle {K : DMod} {M : ModuleCat R} (i : ℤ)
    (α : K ⟶ (single i).obj M) : (H i).obj K ⟶ M :=
  (H i).map α ≫
    ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) i).app M).hom

end DerivedCategory

/-- The incoming-differential cokernel used by the legacy 0G8Y construction. -/
@[stacks 0G8Y "cokernel of a differential in a pseudo-coherent model"]
noncomputable abbrev differentialCokernel {E : Cpx} (i : ℤ) : ModuleCat R :=
  E.differentialCokernel i

/-- The canonical cochain map from a complex to the degree-`i` single object on its incoming
differential cokernel. -/
@[stacks 0G8Y "differential-cokernel map to a single complex"]
noncomputable def to_single_of_differential_cokernel {E : Cpx} (i : ℤ) :
    E ⟶ (CochainComplex.singleFunctor (ModuleCat R) i).obj
      (differentialCokernel (R := R) (E := E) i) :=
  let π := cokernel.π (E.d (i - 1) i)
  let z := CochainComplex.HomComplex.Cocycle.toSingleMk π
    (add_zero i) (i - 1) (sub_add_cancel i 1)
    (cokernel.condition (E.d (i - 1) i))
  z.homOf

/-- The cokernel-to-single map induces a monomorphism on degree-`i` homology. -/
theorem homologyMap_to_single_of_differential_cokernel_mono {E : Cpx} (i : ℤ) :
    Mono (E.homologyMap (to_single_of_differential_cokernel (R := R) (E := E) i) i) := sorry
-- Proof strategy: identify the induced homology map with the canonical injection from cycles
-- modulo boundaries into the cokernel of the incoming differential.

/-- Passing the cokernel-to-single map to the derived category still induces a monomorphism on
degree-`i` homology. -/
theorem homologyToSingle_Q_map_to_single_of_differential_cokernel_mono
    {E : Cpx} (i : ℤ) :
    Mono (DerivedCategory.homologyToSingle (R := R) i
      (DerivedCategory.Q.map
        (to_single_of_differential_cokernel (R := R) (E := E) i))) := sorry
-- Proof strategy: transport `homologyMap_to_single_of_differential_cokernel_mono` through the
-- canonical comparison between complex homology and homology after applying `DerivedCategory.Q`.

/-- Precomposing a map to a single object by an isomorphism preserves monicity of the induced
homology map. -/
theorem mono_homologyToSingle_precompose_iso
    {K L : DMod} {M : ModuleCat R} (i : ℤ) (e : K ≅ L)
    (β : K ⟶ (single i).obj M)
    (hβ : Mono (DerivedCategory.homologyToSingle (R := R) i β)) :
    Mono (DerivedCategory.homologyToSingle (R := R) i (e.inv ≫ β)) := sorry
-- Proof strategy: expand `homologyToSingle`, use functoriality of homology, and observe that the
-- new map is the old monomorphism precomposed with the isomorphism obtained from `e.inv`.

namespace DerivedCategory.IsPseudoCoherent

/-- Lemma 15.66.6 (0G8Y): every degree of a pseudo-coherent derived module embeds into a
finitely presented module through a morphism to the corresponding single object. -/
@[stacks 0G8Y]
theorem exists_finitelyPresented_single_mono
    {K : DMod} (hK : K.IsPseudoCoherent) (i : ℤ) :
    ∃ (M : ModuleCat R) (_ : Module.FinitePresentation R M)
      (α : K ⟶ (single i).obj M),
      Mono (DerivedCategory.homologyToSingle (R := R) i α) := sorry
-- Proof strategy: choose a bounded-above termwise finite-free model of `K`; its incoming
-- differential cokernel is finitely presented, and the explicit map above is homology-monic.
-- Transport that map to `K` along the model isomorphism.

end DerivedCategory.IsPseudoCoherent

end

end CategoryTheory
