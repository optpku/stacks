module

public import stacks_project.Chap10.Lemma_10_110_3.ResolutionData
public import ReasLib.Algebra.Homology.ChainComplex.Exact.Biproduct
public import ReasLib.Algebra.Homology.ChainComplex.Exact.ModuleCat
public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.Concentrated
public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.IdentityDisk
public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.Coordinates
public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.LocalRing
public import ReasLib.Algebra.Homology.ChainComplex.ModuleSingle
import StacksCheckRecall

/-!
# Lemma 10.110.3: minimal free resolutions over local rings

@stack 00OA
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing FiniteFreeComplex

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

-- Local declaration justification (source-local notation): this is the degree-zero target used
-- throughout the minimal-resolution comparison; keeping it local avoids a chapter-wide alias.
local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: a bounded finite free resolution of the residue field can be
minimalized so that every matrix entry of every differential lies in the maximal ideal. -/
lemma exists_minimal_residueField_finiteFreeComplex
    {e : ℕ} (C : FiniteFreeComplex R e)
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ) :
    ∃ (Cmin : FiniteFreeComplex R e)
      (ρmin : Cmin.toChainComplex ⟶ moduleSingle[R] (ResidueField R)),
      ChainComplex.IsFiniteFreeResolution ρmin ∧
        ∀ i : Fin e, ∀ a : Fin (Cmin.rank i.succ), ∀ b : Fin (Cmin.rank i.castSucc),
          FiniteFreeComplex.diffEntry Cmin i a b ∈ maximalIdeal R := sorry
/-! Public support API checks for Lemma 10.110.3. -/

@[stacks 00OA "canonical positive-degree rank measure"]
#check @FiniteFreeComplex.positiveRankSum
@[stacks 00OA "concentration in degree zero from a vanishing rank measure"]
#check @FiniteFreeComplex.positiveRankSum.nonempty_iso_single₀_of_eq_zero
@[stacks 00OA "strict decrease of the split rank profile"]
#check @FiniteFreeComplex.splitRank.positiveRankSumProfile_lt
@[stacks 00OA "exactness inherited by the first biproduct summand"]
#check @HomologicalComplex.ExactAt.of_biprod_fst
@[stacks 00OA "module-chain exactness criterion"]
#check @HomologicalComplex.ExactAt.function_exact_iff
@[stacks 00OA "injectivity from exactness and a zero next term"]
#check @HomologicalComplex.ExactAt.d_injective_of_isZero_next
@[stacks 00OA "coordinate differential transport"]
#check @FiniteFreeComplex.diffAt.termIso_inv_apply
@[stacks 00OA "nonunit differential entries in a local ring"]
#check @FiniteFreeComplex.diffEntry_mem_maximal_of_no_unit
@[stacks 00OA "identity disk vanishing away from its supported degrees"]
#check @FiniteFreeComplex.identityDiskComplex.isZero_X_of_ne_support
@[stacks 00OA "canonical positive component vanishing for a module single"]
#check @ChainComplex.toModuleSingle_f_succ
@[stacks 00OA "existence of a minimal residue-field resolution"]
#check @exists_minimal_residueField_finiteFreeComplex

end
