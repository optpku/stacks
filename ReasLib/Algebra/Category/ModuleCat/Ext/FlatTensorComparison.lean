module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Ext.FlatBaseChange
public import Mathlib.Algebra.Module.FinitePresentation
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
import ReasLib.Algebra.Category.ModuleCat.Ext.TensorComparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat scalar extension for Hom and Ext

@stack 087R

This leaf owns the concrete scalar-extension comparison maps used by Lemma 15.66.4.
Each map first applies exact extension of scalars, then uses the extension-restriction
adjunction and the canonical tensor model of scalar extension.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct

universe u

namespace CategoryTheory.ModuleCat.Ext.FlatTensorComparison

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

set_option maxHeartbeats 5000000

/-- Extension of scalars preserves the zero morphism in the Hom comparison. -/
theorem homImage_zero (M N : ModuleCat R) :
    (ModuleCat.extendScalars (algebraMap R S)).map (0 : M ⟶ N) = 0 := sorry
-- Proof strategy: use that extension of scalars is an additive functor and hence preserves the
-- zero morphism.

/-- Extension of scalars preserves addition in the Hom comparison. -/
theorem homImage_add (M N : ModuleCat R) (g h : M ⟶ N) :
    (ModuleCat.extendScalars (algebraMap R S)).map (g + h) =
      (ModuleCat.extendScalars (algebraMap R S)).map g +
        (ModuleCat.extendScalars (algebraMap R S)).map h := sorry
-- Proof strategy: apply additivity of `ModuleCat.extendScalars` to the pair `g`, `h`.

/-- The additive map on Hom groups induced by extension of scalars. -/
@[stacks 087R "Hom image under scalar extension"]
noncomputable def homImage (M N : ModuleCat R) :
    (M ⟶ N) →+
      ((ModuleCat.extendScalars (algebraMap R S)).obj M ⟶
        (ModuleCat.extendScalars (algebraMap R S)).obj N) :=
  { toFun := (ModuleCat.extendScalars (algebraMap R S)).map
    map_zero' := homImage_zero M N
    map_add' := homImage_add M N }

/-- The Hom image commutes with the restricted `R`-scalar action. -/
theorem homImage_commutes (M N : ModuleCat R) (r : R) :
    AddCommGrpCat.ofHom (homImage (R := R) (S := S) M N) ≫
        ((ModuleCat.restrictScalars (algebraMap R S)).obj
          (ModuleCat.of S
            ((ModuleCat.extendScalars (algebraMap R S)).obj M ⟶
              (ModuleCat.extendScalars (algebraMap R S)).obj N))).smul r =
      (ModuleCat.of R (M ⟶ N)).smul r ≫
        AddCommGrpCat.ofHom (homImage (R := R) (S := S) M N) := sorry
-- Proof strategy: evaluate both sides on a morphism and use the explicit tensor model for
-- extension of scalars to identify extension of `r • f` with `algebraMap R S r • map f`.

/-- The restriction-side Hom comparison before adjunction. -/
@[stacks 087R "restriction-side Hom comparison"]
noncomputable def homComparisonAdjoint (M N : ModuleCat R) :
    ModuleCat.of R (M ⟶ N) ⟶
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        (ModuleCat.of S
          ((ModuleCat.extendScalars (algebraMap R S)).obj M ⟶
            (ModuleCat.extendScalars (algebraMap R S)).obj N)) :=
  ModuleCat.homMk
    (AddCommGrpCat.ofHom (homImage (R := R) (S := S) M N))
    (homImage_commutes (R := R) (S := S) M N)

/-- The Hom comparison on the categorical extension-of-scalars object. -/
@[stacks 087R "categorical Hom base-change comparison"]
noncomputable def homComparisonCore (M N : ModuleCat R) :
    (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R (M ⟶ N)) ⟶
      ModuleCat.of S
        ((ModuleCat.extendScalars (algebraMap R S)).obj M ⟶
          (ModuleCat.extendScalars (algebraMap R S)).obj N) :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).homEquiv
    (ModuleCat.of R (M ⟶ N))
    (ModuleCat.of S
      ((ModuleCat.extendScalars (algebraMap R S)).obj M ⟶
        (ModuleCat.extendScalars (algebraMap R S)).obj N))).symm
      (homComparisonAdjoint (R := R) (S := S) M N)

/-- The canonical Hom base-change comparison `S ⊗[R] Hom_R(M, N) → Hom_S(S ⊗ M, S ⊗ N)`. -/
@[stacks 087R "Hom base-change comparison"]
noncomputable def homComparison (M N : ModuleCat R) :
    ModuleCat.of S (TensorProduct R S (M ⟶ N)) ⟶
      ModuleCat.of S
        ((ModuleCat.extendScalars (algebraMap R S)).obj M ⟶
          (ModuleCat.extendScalars (algebraMap R S)).obj N) :=
  (ModuleCat.ExtendScalars.tensorIso
    (R := R) (S := S) (ModuleCat.of R (M ⟶ N))).inv ≫
      homComparisonCore (R := R) (S := S) M N

/-- The direct flat Ext image commutes with the restricted `R`-scalar action. -/
theorem extImage_commutes (M N : ModuleCat R) (hf : (algebraMap R S).Flat)
    (i : ℕ) (r : R) :
    AddCommGrpCat.ofHom
        (ModuleCat.Ext.FlatBaseChange.map (algebraMap R S) M N hf i) ≫
        ((ModuleCat.restrictScalars (algebraMap R S)).obj
          (ModuleCat.of S
            (Ext ((ModuleCat.extendScalars (algebraMap R S)).obj M)
              ((ModuleCat.extendScalars (algebraMap R S)).obj N) i))).smul r =
      (ModuleCat.of R (Ext M N i)).smul r ≫
        AddCommGrpCat.ofHom
          (ModuleCat.Ext.FlatBaseChange.map (algebraMap R S) M N hf i) := sorry
-- Proof strategy: specialize target naturality of `FlatBaseChange.map` to scalar multiplication
-- by `r` and rewrite extension of that scalar as multiplication by `algebraMap R S r`.

/-- The restriction-side Ext comparison before adjunction. -/
@[stacks 087R "restriction-side Ext comparison"]
noncomputable def extComparisonAdjoint (M N : ModuleCat R)
    (hf : (algebraMap R S).Flat) (i : ℕ) :
    ModuleCat.of R (Ext M N i) ⟶
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        (ModuleCat.of S
          (Ext ((ModuleCat.extendScalars (algebraMap R S)).obj M)
            ((ModuleCat.extendScalars (algebraMap R S)).obj N) i)) :=
  ModuleCat.homMk
    (AddCommGrpCat.ofHom
      (ModuleCat.Ext.FlatBaseChange.map (algebraMap R S) M N hf i))
    (fun r : R => extImage_commutes (R := R) (S := S) M N hf i r)

/-- The Ext comparison on the categorical extension-of-scalars object. -/
@[stacks 087R "categorical Ext base-change comparison"]
noncomputable def extComparisonCore (M N : ModuleCat R)
    (hf : (algebraMap R S).Flat) (i : ℕ) :
    (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R (Ext M N i)) ⟶
      ModuleCat.of S
        (Ext ((ModuleCat.extendScalars (algebraMap R S)).obj M)
          ((ModuleCat.extendScalars (algebraMap R S)).obj N) i) :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).homEquiv
    (ModuleCat.of R (Ext M N i))
    (ModuleCat.of S
      (Ext ((ModuleCat.extendScalars (algebraMap R S)).obj M)
        ((ModuleCat.extendScalars (algebraMap R S)).obj N) i))).symm
      (extComparisonAdjoint (R := R) (S := S) M N hf i)

/-- The canonical Ext base-change comparison `S ⊗[R] Ext_R^i(M, N) → Ext_S^i(S ⊗ M, S ⊗ N)`. -/
@[stacks 087R "Ext base-change comparison"]
noncomputable def extComparison (M N : ModuleCat R)
    (hf : (algebraMap R S).Flat) (i : ℕ) :
    ModuleCat.of S (TensorProduct R S (Ext M N i)) ⟶
      ModuleCat.of S
        (Ext ((ModuleCat.extendScalars (algebraMap R S)).obj M)
          ((ModuleCat.extendScalars (algebraMap R S)).obj N) i) :=
  (ModuleCat.ExtendScalars.tensorIso
    (R := R) (S := S) (ModuleCat.of R (Ext M N i))).inv ≫
      extComparisonCore (R := R) (S := S) M N hf i

/-- Lemma 15.66.4 (1): flat finite-presentation Hom base change is invertible. -/
@[stacks 087R "Lemma 15.66.4 (1)"]
theorem homComparison_isIso_of_finitePresentation
    (M N : ModuleCat R) [Module.FinitePresentation R M]
    (hf : (algebraMap R S).Flat) : IsIso (homComparison (R := R) (S := S) M N) := sorry
-- Proof strategy: factor `homComparison` through the 087Q tensor-Hom comparison with tensor
-- factor `S`, then use the extension-restriction adjunction and the canonical tensor model of
-- extension of scalars; every remaining factor is an isomorphism.

/-- Lemma 15.66.4 (2): flat pseudo-coherent Ext base change is invertible below the coherence
bound. -/
@[stacks 087R "Lemma 15.66.4 (2)"]
theorem extComparison_isIso_of_isMPseudoCoherent
    (M N : ModuleCat R) (m i : ℕ) (hf : (algebraMap R S).Flat)
    (hM : M.IsMPseudoCoherent (-(m : ℤ))) (hi : i < m) :
    IsIso (extComparison (R := R) (S := S) M N hf i) := sorry
-- Proof strategy: factor the comparison as the 087Q Ext tensor comparison followed by the
-- canonical flat-base-change equivalence, and apply pseudo-coherence in degree `i < m`.

/-- Lemma 15.66.4, final assertion: over a Noetherian ring, finite-source Ext base change is
invertible in every degree. -/
@[stacks 087R "Lemma 15.66.4, final assertion"]
theorem extComparison_isIso_of_isNoetherianRing_of_finite
    [IsNoetherianRing R] (M N : ModuleCat R) [Module.Finite R M]
    (hf : (algebraMap R S).Flat) (i : ℕ) :
    IsIso (extComparison (R := R) (S := S) M N hf i) := sorry
-- Proof strategy: over a Noetherian ring a finite module is `(-m)`-pseudo-coherent for every
-- natural cutoff `m`; apply `extComparison_isIso_of_isMPseudoCoherent` with `m = i + 1`.

end CategoryTheory.ModuleCat.Ext.FlatTensorComparison
