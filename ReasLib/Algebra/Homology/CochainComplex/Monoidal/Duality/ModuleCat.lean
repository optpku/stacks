/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed.ModuleCat.Dualizable
public import ReasLib.CategoryTheory.Monoidal.Duality.Module

/-!
# Exact pairings of module cochain complexes

An exact pairing of module cochain complexes restricts on total degree zero to exact pairings of
opposite homogeneous degrees.  This file owns the concrete diagonal projection and the resulting
degreewise pairing, together with boundedness, finite-projectivity, and linear-dual consequences.
The pairing is passed explicitly, so consumers do not need temporary instances.

@stack 0FNK
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open ComplexShape HomologicalComplex

namespace CategoryTheory.CochainComplex.Duality

variable {R : Type u} [CommRing R]
variable {M N : CochainComplex (ModuleCat R) ℤ}

/-- The tensor summand in bidegree `(i,j)`. -/
@[stacks 0FNK "tensor summand in a totalized module complex"]
abbrev tensorSummand
    (M N : CochainComplex (ModuleCat R) ℤ) (i j : ℤ) : ModuleCat R :=
  ((curriedTensor (ModuleCat R)).obj (M.X i)).obj (N.X j)

/-- Projection from total tensor degree zero to the summand in bidegree `(n,-n)`. -/
@[stacks 0FNK "diagonal projection from a tensor totalization"]
noncomputable def diagonalProjection
    (M N : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    ((M ⊗ N).X 0) ⟶ tensorSummand M N n (-n) :=
  HomologicalComplex.mapBifunctorDesc fun i j _ ↦
    if hi : i = n then
      if hj : j = -n then
        eqToHom (congrArg₂ (tensorSummand M N) hi hj)
      else 0
    else 0

/-- The degree-`(n,-n)` coevaluation extracted from an exact pairing of cochain complexes. -/
@[stacks 0FNK "degreewise coevaluation of an exact pairing"]
noncomputable def degreewiseCoevaluation
    (p : ExactPairing M N) (n : ℤ) :
    𝟙_ (ModuleCat R) ⟶ (M.X n ⊗ N.X (-n) : ModuleCat R) :=
  (singleObjXSelf (up ℤ) (0 : ℤ) (𝟙_ (ModuleCat R))).inv ≫
    p.coevaluation'.f 0 ≫ diagonalProjection M N n

/-- The degree-`(-n,n)` evaluation extracted from an exact pairing of cochain complexes. -/
@[stacks 0FNK "degreewise evaluation of an exact pairing"]
noncomputable def degreewiseEvaluation
    (p : ExactPairing M N) (n : ℤ) :
    (N.X (-n) ⊗ M.X n : ModuleCat R) ⟶ 𝟙_ (ModuleCat R) :=
  ιTensorObj N M (-n) n 0 (neg_add_cancel n) ≫
    p.evaluation'.f 0 ≫
      (singleObjXSelf (up ℤ) (0 : ℤ) (𝟙_ (ModuleCat R))).hom

/-- Restricting a complex exact pairing to bidegree `(n,-n)` gives an exact pairing of the
corresponding terms. -/
@[stacks 0FNK "degreewise exact pairing", implicit_reducible]
noncomputable def degreewise (p : ExactPairing M N) (n : ℤ) :
    ExactPairing (M.X n : ModuleCat R) (N.X (-n) : ModuleCat R) where
  coevaluation' := degreewiseCoevaluation p n
  evaluation' := degreewiseEvaluation p n
  coevaluation_evaluation' := sorry
  evaluation_coevaluation' := sorry

/-- The coevaluation at degree `-n`, reindexed so that its second term is literally `N^n`. -/
@[stacks 0FNK "reindexed degreewise coevaluation"]
noncomputable def degreewiseNegCoevaluation (p : ExactPairing M N) (n : ℤ) :
    𝟙_ (ModuleCat R) ⟶ (M.X (-n) ⊗ N.X n : ModuleCat R) :=
  degreewiseCoevaluation p (-n) ≫
    (𝟙 (M.X (-n) : ModuleCat R) ⊗ₘ eqToHom (congrArg N.X (neg_neg n)))

/-- The evaluation at degree `-n`, reindexed so that its first term is literally `N^n`. -/
@[stacks 0FNK "reindexed degreewise evaluation"]
noncomputable def degreewiseNegEvaluation (p : ExactPairing M N) (n : ℤ) :
    (N.X n ⊗ M.X (-n) : ModuleCat R) ⟶ 𝟙_ (ModuleCat R) :=
  (eqToHom (congrArg N.X (neg_neg n)).symm ⊗ₘ 𝟙 (M.X (-n) : ModuleCat R)) ≫
    degreewiseEvaluation p (-n)

/-- The degreewise pairing at `-n`, with its second term transported from degree `-(-n)` to
degree `n`. -/
@[stacks 0FNK "reindexed degreewise exact pairing", implicit_reducible]
noncomputable def degreewiseNeg (p : ExactPairing M N) (n : ℤ) :
    ExactPairing (M.X (-n) : ModuleCat R) (N.X n : ModuleCat R) where
  coevaluation' := degreewiseNegCoevaluation p n
  evaluation' := degreewiseNegEvaluation p n
  coevaluation_evaluation' := sorry
  evaluation_coevaluation' := sorry

/-- The first complex in an exact pairing of module complexes is bounded. -/
@[stacks 0FNK "boundedness of a dualizable module complex"]
theorem left_bounded (p : ExactPairing M N) :
    CochainComplex.bounded (ModuleCat R) M := sorry

/-- The second complex in an exact pairing of module complexes is bounded. -/
@[stacks 0FNK "boundedness of a dualizable module complex"]
theorem right_bounded (p : ExactPairing M N) :
    CochainComplex.bounded (ModuleCat R) N := sorry

/-- Every term of the first complex in an exact pairing is finite projective. -/
@[stacks 0FNK "finite-projective terms of a dualizable module complex"]
theorem left_finiteProjective (p : ExactPairing M N) (n : ℤ) :
    Module.FiniteProjective R (M.X n) := sorry

/-- Every term of the second complex in an exact pairing is finite projective. -/
@[stacks 0FNK "finite-projective terms of a dualizable module complex"]
theorem right_finiteProjective (p : ExactPairing M N) (n : ℤ) :
    Module.FiniteProjective R (N.X n) := sorry

/-- Evaluation in degree `n` identifies `N^n` with a functional on `M^{-n}`. -/
@[stacks 0FNK "degreewise map to the linear dual"]
noncomputable def rightTermHom (p : ExactPairing M N) (n : ℤ) :
    N.X n ⟶ ModuleCat.of R (Module.Dual R (M.X (-n))) :=
  ExactPairing.toModuleDualOfEvaluation (degreewiseNegEvaluation p n)

/-- Coevaluation in degree `-n` sends a functional on `M^{-n}` back to `N^n`. -/
@[stacks 0FNK "degreewise map from the linear dual"]
def rightTermInv (p : ExactPairing M N) (n : ℤ) :
    ModuleCat.of R (Module.Dual R (M.X (-n))) ⟶ N.X n :=
  ExactPairing.fromCoevaluation (degreewiseNegCoevaluation p n)

/-- The term `N^n` is canonically the linear dual of `M^{-n}`.  Both maps are explicit in the
degreewise evaluation and coevaluation; only their inverse laws use the triangle identities. -/
@[stacks 0FNK "degreewise linear-dual identification"]
noncomputable def rightTermIso (p : ExactPairing M N) (n : ℤ) :
    N.X n ≅ ModuleCat.of R (Module.Dual R (M.X (-n))) where
  hom := rightTermHom p n
  inv := rightTermInv p n
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Under the degreewise dual identifications, the differential on the second complex is the
signed transpose of the differential on the first complex. -/
@[stacks 0FNK "signed transpose differential on a dual complex"]
theorem rightTermIso_d_comm (p : ExactPairing M N) (n : ℤ) :
    CommSq (N.d n (n + 1))
      (rightTermIso p n).hom
      (rightTermIso p (n + 1)).hom
      ((-n.negOnePow) •
        ModuleCat.ofHom
          ((LinearMap.dualMap (ModuleCat.Hom.hom (M.d (-(n + 1)) (-n)))) :
            Module.Dual R (M.X (-n)) →ₗ[R] Module.Dual R (M.X (-(n + 1))))) := sorry

end CategoryTheory.CochainComplex.Duality
