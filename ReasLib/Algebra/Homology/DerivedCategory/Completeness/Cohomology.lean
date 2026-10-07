module

public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
public import ReasLib.RingTheory.AdicCompletion.CompleteTarget
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology of derived completion over a Noetherian ring

When every cohomology module of a derived object is finite, the cohomology of its derived
completion is canonically the ordinary adic completion of its cohomology.

@stack 0A06
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

-- Local instance justification (search instability): expose the standard derived localization
-- only while constructing the cohomology comparison in this file.
attribute [local instance] HasDerivedCategory.standard

namespace DerivedCategory.DerivedCompletion.Cohomology

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

-- Local declaration justification (source-local notation): abbreviate the fixed module-derived
-- category used by this cohomology comparison without changing the public owner namespace.
local notation "DMod" => DerivedCategory (ModuleCat A)
-- Local declaration justification (source-local notation): abbreviate the selected homology
-- functor in the retained source-facing degree statements.
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)

/-- Under finite cohomology, the target of the ordinary-to-derived completion comparison is
adic complete. -/
@[stacks 0A06 "adic completeness of derived-completion cohomology"]
theorem target_isAdicComplete
    (I : Ideal A) (K : DMod) (n : ℤ)
    (hK : ∀ i : ℤ, Module.Finite A ((H i).obj K)) :
    IsAdicComplete I ((H n).obj (K^∧[I, I.fg_of_isNoetherianRing])) := sorry
-- Proof strategy: use the completion Milnor sequence and Noetherian Artin-Rees to identify
-- the target with the inverse limit of its finite ideal-power quotients.

/-- The canonical map from the ordinary adic completion of `H^n(K)` to `H^n(K^∧)`. -/
@[stacks 0A06 "ordinary-to-derived cohomology comparison map"]
noncomputable def comparison
    (I : Ideal A) (K : DMod) (n : ℤ)
    (hK : ∀ i : ℤ, Module.Finite A ((H i).obj K)) :
    ModuleCat.of A (AdicCompletion I ((H n).obj K)) ⟶
      (H n).obj (K^∧[I, I.fg_of_isNoetherianRing]) :=
  -- Local instance justification (proof-local temporary data): install the named completeness
  -- proof only while applying the universal map out of ordinary adic completion.
  letI : IsAdicComplete I ((H n).obj (K^∧[I, I.fg_of_isNoetherianRing])) :=
    target_isAdicComplete I K n hK
  ModuleCat.ofHom <|
    AdicCompletion.mapToComplete I
      ((H n).map (toDerivedCompletion I I.fg_of_isNoetherianRing K)).hom

/-- The cohomology comparison extends the map on cohomology induced by the derived-completion
unit. -/
@[stacks 0A06 "cohomology comparison unit equation"]
theorem of_comp_comparison
    (I : Ideal A) (K : DMod) (n : ℤ)
    (hK : ∀ i : ℤ, Module.Finite A ((H i).obj K)) :
    ModuleCat.ofHom (AdicCompletion.of I ((H n).obj K)) ≫ comparison I K n hK =
      (H n).map (toDerivedCompletion I I.fg_of_isNoetherianRing K) := sorry
-- Proof strategy: unfold `comparison` and apply the defining equation of
-- `AdicCompletion.mapToComplete` for the installed complete target.

/-- Lemma 15.95.4: if every cohomology module of `K` is finite, then the canonical map from
the ordinary adic completion of `H^n(K)` to `H^n(K^∧)` is an isomorphism. -/
@[stacks 0A06 "cohomology of Noetherian derived completion"]
theorem comparison_isIso
    (I : Ideal A) (K : DMod) (n : ℤ)
    (hK : ∀ i : ℤ, Module.Finite A ((H i).obj K)) :
    IsIso (comparison I K n hK) := sorry
-- Proof strategy: compare both sides modulo every power of `I` using finite cohomology and
-- Artin-Rees, then invoke completeness and separatedness to conclude that the comparison is an iso.

/-- The canonical isomorphism from `H^n(K^∧)` to the ordinary adic completion of `H^n(K)`. -/
@[stacks 0A06 "cohomology comparison isomorphism data"]
noncomputable def iso
    (I : Ideal A) (K : DMod) (n : ℤ)
    (hK : ∀ i : ℤ, Module.Finite A ((H i).obj K)) :
    (H n).obj (K^∧[I, I.fg_of_isNoetherianRing]) ≅
      ModuleCat.of A (AdicCompletion I ((H n).obj K)) :=
  -- Local instance justification (proof-local temporary data): install invertibility only while
  -- bundling the already named comparison as an isomorphism.
  letI := comparison_isIso I K n hK
  (asIso (comparison I K n hK)).symm

end DerivedCategory.DerivedCompletion.Cohomology
