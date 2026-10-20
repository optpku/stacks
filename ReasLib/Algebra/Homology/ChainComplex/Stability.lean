/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.ShortComplex.Stability

/-!
# Stable Biproducts of Chain Complexes

This leaf transports the stable biproduct construction for short complexes to
`ℕ`-indexed chain complexes.  The primitive construction is the degree-zero
short complex; the only vanishing data needed for its inverse is in degree `2`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

noncomputable section

namespace CategoryTheory.ChainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The second differential of the degree-zero short complex of an
`ℕ`-indexed chain complex vanishes. -/
theorem shortComplexZero_g_eq_zero (A : _root_.ChainComplex C ℕ) :
    (A.sc 0).g = 0 := sorry

/-- A chain homotopy has zero degree-zero short-complex `h₀` component when
the target complex has a zero object in degree `2`. -/
theorem homotopy_toShortComplex_h0_eq_zero
    {A B : _root_.ChainComplex C ℕ} {f g : A ⟶ B}
    (ho : _root_.Homotopy f g) (hB2 : IsZero (B.X 2)) :
    (ho.toShortComplex 0).h₀ = 0 := sorry

end CategoryTheory.ChainComplex

namespace CategoryTheory.ChainComplex.HomotopyEquiv

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {A B : _root_.ChainComplex C ℕ}

/-- The degree-zero short-complex homotopy equivalence induced by a homotopy
equivalence of `ℕ`-indexed chain complexes. -/
noncomputable def toShortComplex (e : _root_.HomotopyEquiv A B) :
    ShortComplex.HomotopyEquiv (A.sc 0) (B.sc 0) where
  hom := (shortComplexFunctor C (ComplexShape.down ℕ) 0).map e.hom
  inv := (shortComplexFunctor C (ComplexShape.down ℕ) 0).map e.inv
  homotopyHomInvId := e.homotopyHomInvId.toShortComplex 0
  homotopyInvHomId := e.homotopyInvHomId.toShortComplex 0

section

variable [HasBinaryBiproducts C]

/-- The canonical transport from the degree-zero short-complex source biproduct
to the degree-one/degree-zero chain-complex biproduct. -/
noncomputable def stableBiprodSourceIso (A B : _root_.ChainComplex C ℕ) :
    (A.sc 0).X₁ ⊞ (B.sc 0).X₂ ≅ A.X 1 ⊞ B.X 0 :=
  biprod.mapIso
    (A.XIsoOfEq (_root_.ChainComplex.prev ℕ 0))
    (B.XIsoOfEq rfl)

/-- The canonical transport from the degree-zero short-complex target biproduct
to the degree-one/degree-zero chain-complex biproduct. -/
noncomputable def stableBiprodTargetIso (A B : _root_.ChainComplex C ℕ) :
    (B.sc 0).X₁ ⊞ (A.sc 0).X₂ ≅ B.X 1 ⊞ A.X 0 :=
  biprod.mapIso
    (B.XIsoOfEq (_root_.ChainComplex.prev ℕ 0))
    (A.XIsoOfEq rfl)

/-- Stacks 00S3: the stable biproduct morphism induced by a homotopy equivalence
of `ℕ`-indexed chain complexes. -/
@[stacks 00S3 "chain-complex stable biproduct morphism"]
noncomputable def stableBiprodHom (e : _root_.HomotopyEquiv A B) :
    A.X 1 ⊞ B.X 0 ⟶ B.X 1 ⊞ A.X 0 :=
  (stableBiprodSourceIso A B).inv ≫
    CategoryTheory.ShortComplex.HomotopyEquiv.stableBiprodHom (toShortComplex e) ≫
      (stableBiprodTargetIso A B).hom

/-- The short-complex stable biproduct isomorphism associated to a homotopy
equivalence of chain complexes with zero objects in degree `2`. -/
noncomputable def stableBiprodShortIso
    (e : _root_.HomotopyEquiv A B) (hA2 : IsZero (A.X 2)) (hB2 : IsZero (B.X 2)) :
    (A.sc 0).X₁ ⊞ (B.sc 0).X₂ ≅ (B.sc 0).X₁ ⊞ (A.sc 0).X₂ :=
  CategoryTheory.ShortComplex.HomotopyEquiv.stableBiprodIso
    (toShortComplex e)
    (CategoryTheory.ChainComplex.shortComplexZero_g_eq_zero A)
    (CategoryTheory.ChainComplex.shortComplexZero_g_eq_zero B)
    (CategoryTheory.ChainComplex.homotopy_toShortComplex_h0_eq_zero
      e.homotopyHomInvId hA2)
    (CategoryTheory.ChainComplex.homotopy_toShortComplex_h0_eq_zero
      e.homotopyInvHomId hB2)

/-- The explicit inverse of the chain-complex stable biproduct morphism when
the degree-`2` terms are zero objects. -/
noncomputable def stableBiprodInv
    (e : _root_.HomotopyEquiv A B) (hA2 : IsZero (A.X 2)) (hB2 : IsZero (B.X 2)) :
    B.X 1 ⊞ A.X 0 ⟶ A.X 1 ⊞ B.X 0 :=
  (stableBiprodTargetIso A B).inv ≫
    (stableBiprodShortIso e hA2 hB2).inv ≫
      (stableBiprodSourceIso A B).hom

/-- Under vanishing in degree `2`, the explicit stable biproduct maps compose to
the identity on `A.X 1 ⊞ B.X 0`. -/
theorem stableBiprodHom_comp_stableBiprodInv
    (e : _root_.HomotopyEquiv A B) (hA2 : IsZero (A.X 2)) (hB2 : IsZero (B.X 2)) :
    stableBiprodHom e ≫ stableBiprodInv e hA2 hB2 = 𝟙 (A.X 1 ⊞ B.X 0) := sorry

/-- Under vanishing in degree `2`, the explicit stable biproduct maps compose to
the identity on `B.X 1 ⊞ A.X 0`. -/
theorem stableBiprodInv_comp_stableBiprodHom
    (e : _root_.HomotopyEquiv A B) (hA2 : IsZero (A.X 2)) (hB2 : IsZero (B.X 2)) :
    stableBiprodInv e hA2 hB2 ≫ stableBiprodHom e = 𝟙 (B.X 1 ⊞ A.X 0) := sorry

/-- Stacks 00S3: the explicit stable biproduct isomorphism associated to a
homotopy equivalence whose degree-`2` terms are zero objects. -/
@[stacks 00S3 "chain-complex stable biproduct isomorphism"]
noncomputable def stableBiprodIso
    (e : _root_.HomotopyEquiv A B) (hA2 : IsZero (A.X 2)) (hB2 : IsZero (B.X 2)) :
    A.X 1 ⊞ B.X 0 ≅ B.X 1 ⊞ A.X 0 where
  hom := stableBiprodHom e
  inv := stableBiprodInv e hA2 hB2
  hom_inv_id := stableBiprodHom_comp_stableBiprodInv e hA2 hB2
  inv_hom_id := stableBiprodInv_comp_stableBiprodHom e hA2 hB2

/-- The stable biproduct morphism is invertible when the degree-`2` terms of
both chain complexes are zero objects. -/
theorem stableBiprodHom_isIso_of_isZero_two
    (e : _root_.HomotopyEquiv A B) (hA2 : IsZero (A.X 2)) (hB2 : IsZero (B.X 2)) :
    IsIso (stableBiprodHom e) := sorry

/-- Lemma 10.134.14 (Stacks 00S3): a homotopy equivalence between chain
complexes concentrated in degrees `0` and `1` induces an invertible stable
biproduct morphism.  This is the source-shaped specialization of the
degree-`2` vanishing API. -/
@[stacks 00S3]
theorem stableBiprodHom_isIso_of_concentrated
    (hA : ∀ n : ℕ, n ≠ 0 → n ≠ 1 → IsZero (A.X n))
    (hB : ∀ n : ℕ, n ≠ 0 → n ≠ 1 → IsZero (B.X n))
    (e : _root_.HomotopyEquiv A B) :
    IsIso (stableBiprodHom e) := sorry

end

end CategoryTheory.ChainComplex.HomotopyEquiv
