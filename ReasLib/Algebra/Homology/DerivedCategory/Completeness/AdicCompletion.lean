module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.LocalizationAway.Module
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.Algebra.Module.LocalizedModule.Away
public import ReasLib.RingTheory.AdicCompletion.IdealGenerators
import Mathlib.Tactic.CrossRefAttribute

/-!
# Adic completeness and derived completeness

This leaf owns the module-level comparison between ordinary adic completeness and derived
completeness.  The forward implication is valid for every ideal; the converse retains the finite
generation needed for surjectivity of the ordinary completion map.

@stack 091R
@stack 0EEU
-/

@[expose] public section

noncomputable section

universe u v

namespace ModuleCat

variable {A : Type u} [CommRing A]
variable {I : Ideal A} (M : ModuleCat.{max u v, u} A)

/-- Lemma 15.92.3 (Stacks `091R`) (1): an `I`-adically complete module is derived complete with
respect to `I`; equivalently, its localization-away object vanishes at every `f ∈ I`. -/
@[stacks 091R "adic completeness implies derived completeness"]
theorem isDerivedCompleteWithRespectTo_of_isAdicComplete
    (hcomplete : IsAdicComplete I M) :
    M.IsDerivedCompleteWithRespectTo I := sorry
-- Proof strategy: for every `f ∈ I`, use ordinary completeness to show the localization-away
-- tensor tower vanishes, then apply the localization-away characterization of derived completeness.

/-- Lemma 15.92.3 (Stacks `091R`) (2): for a finitely generated ideal, derived completeness of a
module implies surjectivity of its ordinary adic-completion map. -/
@[stacks 091R "derived completeness implies surjective adic completion"]
theorem surjective_adicCompletion_of_isDerivedCompleteWithRespectTo
    (hfg : I.FG) (hM : M.IsDerivedCompleteWithRespectTo I) :
    Function.Surjective (AdicCompletion.of I M) := sorry
-- Proof strategy: choose finite generators for `I`, use derived completeness to kill the
-- corresponding Cech obstruction, and identify the resulting inverse-limit map with `AdicCompletion.of`.

end ModuleCat

namespace DerivedCategory.DerivedCompletion.Adic

open CategoryTheory
open scoped TensorProduct

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)

/- The ordinary completion object is the target of the universal map from derived completion. -/
/-- 0EEU: The degree-zero object on an ordinary adic completion is derived complete. -/
@[stacks 0EEU "ordinary adic completion is derived complete"]
theorem target_isDerivedComplete
    (I : Ideal A) (hI : I.FG) (M : Type u) [AddCommGroup M] [Module A M] :
    ((ModuleCat.single0Functor : ModuleCat A ⥤ DMod).obj
      (ModuleCat.of A (AdicCompletion I M))).IsDerivedCompleteWithRespectTo I := sorry
-- Proof strategy: apply `ModuleCat.isDerivedCompleteWithRespectTo_of_isAdicComplete` to the
-- canonical completeness instance of `AdicCompletion I M`.

/- The comparison is concrete: its map is the universal lift of the ordinary completion map. -/
/-- 0EEU: The canonical map from the derived completion of `M[0]` to the degree-zero ordinary
adic completion of `M`. -/
@[stacks 0EEU "adic completion comparison map"]
noncomputable def comparison
    (I : Ideal A) (hI : I.FG) (M : Type u) [AddCommGroup M] [Module A M] :
    DerivedCategory.derivedCompletionOf I hI
        ((ModuleCat.single0Functor : ModuleCat A ⥤ DMod).obj (ModuleCat.of A M)) ⟶
      (ModuleCat.single0Functor : ModuleCat A ⥤ DMod).obj
        (ModuleCat.of A (AdicCompletion I M)) :=
  DerivedCategory.DerivedCompletion.lift I hI
    (K := (ModuleCat.single0Functor : ModuleCat A ⥤ DMod).obj (ModuleCat.of A M))
    (L := (ModuleCat.single0Functor : ModuleCat A ⥤ DMod).obj
      (ModuleCat.of A (AdicCompletion I M)))
    (target_isDerivedComplete I hI M)
    ((ModuleCat.single0Functor : ModuleCat A ⥤ DMod).map
      (ModuleCat.ofHom (AdicCompletion.of I M) :
        ModuleCat.of A M ⟶ ModuleCat.of A (AdicCompletion I M)))

/-- 0EEU: The finite-flat tensor comparison is invertible. -/
@[stacks 0EEU "finite-flat tensor comparison is an isomorphism"]
theorem comparison_isIso_of_finite_tensor_flat
    (I : Ideal A) (hI : I.FG)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (N : Type u) [AddCommGroup N] [Module A N] [Module.Flat A N] :
    IsIso (comparison I hI (M ⊗[A] N)) := sorry
-- Proof strategy: flatness identifies every ideal-power quotient tensor stage with the
-- ordinary quotient of `M ⊗ N`; finite generation and Artin-Rees identify the derived limit
-- with its ordinary adic completion.

/-- 0EEU: The comparison for a finite module after localization away from one element is
invertible. -/
@[stacks 0EEU "localized finite comparison is an isomorphism"]
theorem comparison_isIso_localizationAway_of_finite
    (I : Ideal A) (hI : I.FG)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (f : A) :
    IsIso (comparison I hI (LocalizedModule.Away f M)) := sorry
-- Proof strategy: specialize `comparison_isIso_of_finite_tensor_flat` to the flat localization
-- module and use the canonical localized-module tensor equivalence.

/-- 0EEU: The adic completion comparison is characterized by the ordinary completion map. -/
@[reassoc (attr := simp), stacks 0EEU "adic completion comparison unit equation"]
theorem toDerivedCompletion_comp_comparison
    (I : Ideal A) (hI : I.FG) (M : Type u) [AddCommGroup M] [Module A M] :
    DerivedCategory.toDerivedCompletion I hI
          ((ModuleCat.single0Functor : ModuleCat A ⥤ DMod).obj (ModuleCat.of A M)) ≫
        comparison I hI M =
      ((ModuleCat.single0Functor : ModuleCat A ⥤ DMod).map
        (ModuleCat.ofHom (AdicCompletion.of I M) :
          ModuleCat.of A M ⟶ ModuleCat.of A (AdicCompletion I M))) := sorry
-- Proof strategy: unfold `comparison` and use the defining factorization equation of
-- `DerivedCategory.DerivedCompletion.lift`.

end DerivedCategory.DerivedCompletion.Adic
