module

public import ReasLib.CategoryTheory.Homology.ChainShift
public import ReasLib.CategoryTheory.Homology.Homotopy.CochainShift
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Homotopies and Shifts of Chain Complexes

Reindexing by integer negation transports the cochain self-homotopy description to chain
complexes, where self-homotopies correspond to maps into the `1`-shifted target.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace ChainComplex

noncomputable section

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace ChainCochain

namespace Homotopy

/-- The component family obtained by reindexing a chain homotopy along integer negation. -/
def toCochainHom {A B : ChainComplex C ℤ} {a b : A ⟶ B}
    (h : Homotopy a b) (p q : ℤ) :
    ((chainToCochain C).obj A).X p ⟶ ((chainToCochain C).obj B).X q :=
  h.hom (-p) (-q)

/-- Reindexing a chain homotopy along negation preserves its shape condition. -/
theorem toCochainHom_zero {A B : ChainComplex C ℤ} {a b : A ⟶ B}
    (h : Homotopy a b) (p q : ℤ) (hpq : ¬(ComplexShape.up ℤ).Rel q p) :
    toCochainHom h p q = 0 := sorry

/-- Reindexing a chain homotopy along negation preserves the homotopy equation. -/
theorem toCochainHom_comm {A B : ChainComplex C ℤ} {a b : A ⟶ B}
    (h : Homotopy a b) (p : ℤ) :
    ((chainToCochain C).map a).f p =
      dNext p (toCochainHom h) +
        prevD p (toCochainHom h) +
          ((chainToCochain C).map b).f p := sorry

/-- Reindex a chain homotopy as a cochain homotopy by negating degrees. -/
def toCochain {A B : ChainComplex C ℤ} {a b : A ⟶ B}
    (h : Homotopy a b) :
    Homotopy ((chainToCochain C).map a) ((chainToCochain C).map b) :=
  Homotopy.mk (toCochainHom h)
    (toCochainHom_zero h) (toCochainHom_comm h)

/-- The component family obtained by transporting a reindexed cochain homotopy back to chain
degrees. -/
def toChainHom {A B : ChainComplex C ℤ} {a b : A ⟶ B}
    (h : Homotopy ((chainToCochain C).map a) ((chainToCochain C).map b))
    (i j : ℤ) : A.X i ⟶ B.X j :=
  (A.XIsoOfEq (Int.neg_neg i).symm).hom ≫ h.hom (-i) (-j) ≫
    (B.XIsoOfEq (Int.neg_neg j)).hom

/-- Transporting a reindexed homotopy back to chains preserves its shape condition. -/
theorem toChainHom_zero {A B : ChainComplex C ℤ} {a b : A ⟶ B}
    (h : Homotopy ((chainToCochain C).map a) ((chainToCochain C).map b))
    (i j : ℤ) (hij : ¬(ComplexShape.down ℤ).Rel j i) :
    toChainHom h i j = 0 := sorry

/-- Transporting a reindexed homotopy back to chains preserves the homotopy equation. -/
theorem toChainHom_comm {A B : ChainComplex C ℤ} {a b : A ⟶ B}
    (h : Homotopy ((chainToCochain C).map a) ((chainToCochain C).map b))
    (i : ℤ) :
    a.f i = dNext i (toChainHom h) +
      prevD i (toChainHom h) + b.f i := sorry

/-- Transport a homotopy of reindexed cochain maps back to the corresponding chain maps. -/
def toChain {A B : ChainComplex C ℤ} {a b : A ⟶ B}
    (h : Homotopy ((chainToCochain C).map a) ((chainToCochain C).map b)) :
    Homotopy a b :=
  Homotopy.mk (toChainHom h)
    (toChainHom_zero h) (toChainHom_comm h)

/-- Reindexing a chain homotopy to cochains and back is the identity. -/
theorem toChain_toCochain {A B : ChainComplex C ℤ} {a b : A ⟶ B}
    (h : Homotopy a b) :
    toChain (toCochain h) = h := sorry

/-- Transporting a reindexed cochain homotopy back to chains and forward is the identity. -/
theorem toCochain_toChain {A B : ChainComplex C ℤ} {a b : A ⟶ B}
    (h : Homotopy ((chainToCochain C).map a) ((chainToCochain C).map b)) :
    toCochain (toChain h) = h := sorry

/-- Reindexing along integer negation gives an equivalence between chain and cochain
homotopies. -/
def equiv {A B : ChainComplex C ℤ} {a b : A ⟶ B} :
    Homotopy a b ≃
      Homotopy ((chainToCochain C).map a) ((chainToCochain C).map b) where
  toFun := toCochain
  invFun := toChain
  left_inv := toChain_toCochain
  right_inv := toCochain_toChain

end Homotopy

namespace Shift

/-- The objectwise shift comparison for reindexing a chain complex as a cochain complex. -/
noncomputable def commIso (K : ChainComplex C ℤ) (k : ℤ) :
    (chainToCochain C).obj (K⟦k⟧) ≅
      (shiftFunctor (cochainShiftPullback C) k).obj ((chainToCochain C).obj K) :=
  ((chainToCochain C).commShiftIso k).app K

/-- Reindexing identifies the `k`-shift of a chain complex with the `(-k)`-shift of the
associated cochain complex. -/
noncomputable def iso (K : ChainComplex C ℤ) (k : ℤ) :
    ((chainToCochain C).obj (K⟦k⟧) : CochainComplex C ℤ) ≅
      (shiftFunctor (CochainComplex C ℤ) (-k)).obj ((chainToCochain C).obj K) :=
  commIso K k ≪≫
    (pullbackShiftIso (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ) k (-k) rfl).app
      ((chainToCochain C).obj K)

/-- Reindexing identifies cochain maps into a `(-k)`-shift with chain maps into the
corresponding `k`-shift. -/
noncomputable def homEquiv (A B : ChainComplex C ℤ) (k : ℤ) :
    (((chainToCochain C).obj A : CochainComplex C ℤ) ⟶
      (shiftFunctor (CochainComplex C ℤ) (-k)).obj ((chainToCochain C).obj B)) ≃
      (A ⟶ B⟦k⟧) :=
  (((chainCochainEquiv C).fullyFaithfulFunctor.homEquiv).trans
    ((Iso.refl _).homCongr (iso B k))).symm

end Shift

end ChainCochain

namespace Homotopy

/-- Self-homotopies of a chain map are canonically maps into the `1`-shifted target. -/
@[stacks 011C]
noncomputable def selfEquivShiftHom {A B : ChainComplex C ℤ} (a : A ⟶ B) :
    Homotopy a a ≃ (A ⟶ B⟦(1 : ℤ)⟧) :=
  ChainCochain.Homotopy.equiv.trans
    ((CochainComplex.Homotopy.selfEquivShiftHom ((chainToCochain C).map a)).trans
      (ChainCochain.Shift.homEquiv A B 1))

/-- Homotopies between two chain maps are either empty or form a principal homogeneous space
under the group of maps into the `1`-shifted target. -/
@[stacks 011C]
theorem isEmpty_or_nonempty_addTorsor {A B : ChainComplex C ℤ} (a b : A ⟶ B) :
    IsEmpty (Homotopy a b) ∨
      Nonempty (AddTorsor (A ⟶ B⟦(1 : ℤ)⟧) (Homotopy a b)) := sorry

end Homotopy

end

end ChainComplex
