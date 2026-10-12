/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.CategoryTheory.Shift.Pullback
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Chain Complex Shift

@stack 011A

The canonical shift on `ChainComplex C ℤ`, obtained by pulling back the cochain-complex shift
along integer negation and transporting across `ChainComplex.cochainComplexEquivalence`.

Mathlib provides `CochainComplex.shiftFunctorObjXIso` but not the chain-complex analogue.
This module fills that gap with the degree-identification API for `K⟦k⟧` in the chain setting.
-/

@[expose] public section

open CategoryTheory HomologicalComplex

universe v u

namespace ChainComplex

noncomputable section

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- The cochain-complex category equipped with the integer shift pulled back along negation. -/
abbrev cochainShiftPullback :=
  PullbackShift (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ)

/-- Reindexing by integer negation identifies chain complexes with the pullback shift owner. -/
abbrev chainCochainEquiv : ChainComplex C ℤ ≌ cochainShiftPullback C :=
  ChainComplex.cochainComplexEquivalence C

/-- The canonical reindexing functor from chain complexes to cochain complexes. -/
abbrev chainToCochain : ChainComplex C ℤ ⥤ cochainShiftPullback C :=
  (chainCochainEquiv C).functor

/-- The inverse reindexing functor from cochain complexes to chain complexes. -/
abbrev cochainToChain : cochainShiftPullback C ⥤ ChainComplex C ℤ :=
  (chainCochainEquiv C).inverse

/-- The chain-complex shift transported from the cochain-complex shift along reindexing. -/
abbrev shiftFunctorAux (k : ℤ) : ChainComplex C ℤ ⥤ ChainComplex C ℤ :=
  chainToCochain C ⋙ shiftFunctor (cochainShiftPullback C) k ⋙ cochainToChain C

/-- The transported shift evaluates in degree `n` as the original complex in degree `n + k`. -/
theorem shiftFunctorAux_obj_X (k : ℤ) (K : ChainComplex C ℤ) (n : ℤ) :
    ((shiftFunctorAux C k).obj K).X n = K.X (n + k) := sorry

/-- The counit comparison defining `shiftFunctorAuxIso` is natural in the chain complex. -/
theorem shiftFunctorAuxIso_naturality (k : ℤ) {K L : ChainComplex C ℤ} (φ : K ⟶ L) :
    ((shiftFunctorAux C k ⋙ chainToCochain C).map φ) ≫
        ((chainCochainEquiv C).counitIso.app
          ((shiftFunctor (cochainShiftPullback C) k).obj ((chainToCochain C).obj L))).hom =
      ((chainCochainEquiv C).counitIso.app
          ((shiftFunctor (cochainShiftPullback C) k).obj ((chainToCochain C).obj K))).hom ≫
        ((chainToCochain C ⋙ shiftFunctor (cochainShiftPullback C) k).map φ) := sorry

/-- Reindexing chain complexes as cochain complexes intertwines the transported shifts. -/
def shiftFunctorAuxIso (k : ℤ) :
    shiftFunctorAux C k ⋙ chainToCochain C ≅
      chainToCochain C ⋙ shiftFunctor (cochainShiftPullback C) k :=
  NatIso.ofComponents
    (fun K ↦ (chainCochainEquiv C).counitIso.app
      ((shiftFunctor (cochainShiftPullback C) k).obj ((chainToCochain C).obj K)))
    (fun φ ↦ shiftFunctorAuxIso_naturality C k φ)

/-- Chain complexes indexed by `ℤ` carry the canonical shift. -/
@[stacks 011A]
noncomputable instance instHasShift : HasShift (ChainComplex C ℤ) ℤ :=
  Functor.FullyFaithful.hasShift
    (Functor.FullyFaithful.ofFullyFaithful _)
    (fun k ↦ shiftFunctorAux C k)
    (fun k ↦ shiftFunctorAuxIso C k)

/-- Reindexing a chain complex as a cochain complex commutes with every integer shift. -/
noncomputable instance instChainToCochainCommShift : (chainToCochain C).CommShift ℤ :=
  Functor.CommShift.ofHasShiftOfFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful (chainToCochain C))
    (shiftFunctorAux C) (shiftFunctorAuxIso C)

variable {C}

/-- The degree-`n` term of the shifted chain complex `K⟦k⟧` is `K.X (n + k)`. -/
theorem shiftFunctor_obj_X (k : ℤ) (K : ChainComplex C ℤ) (n : ℤ) :
    (K⟦k⟧).X n = K.X (n + k) :=
  shiftFunctorAux_obj_X C k K n

/-- The degree identification for a shifted chain complex after replacing `i + k` by an equal
index `j`. -/
theorem shiftFunctor_obj_X_eq (K : ChainComplex C ℤ) (k i j : ℤ) (h : j = i + k) :
    (K⟦k⟧).X i = K.X j := sorry

/-- The canonical degree isomorphism `(K⟦k⟧).X i ≅ K.X j` when `j = i + k`. -/
@[stacks 011A "chain-complex shift degree isomorphism", simp]
def shiftFunctorObjXIso (K : ChainComplex C ℤ) (k i j : ℤ) (h : j = i + k) :
    (K⟦k⟧).X i ≅ K.X j :=
  eqToIso (shiftFunctor_obj_X_eq K k i j h)

/-- Via the canonical degree identifications, the differential of `K⟦k⟧` is the signed
translation of the differential of `K`. -/
theorem shiftFunctor_obj_d (k : ℤ) (K : ChainComplex C ℤ) (i j : ℤ) :
    (K.shiftFunctorObjXIso k i (i + k) rfl).inv ≫ (K⟦k⟧).d i j =
      (k.negOnePow • K.d (i + k) (j + k)) ≫
        (K.shiftFunctorObjXIso k j (j + k) rfl).inv := sorry

/-- Via the canonical degree identifications, shifting a chain map translates its components. -/
theorem shiftFunctor_map_f (k : ℤ) {K L : ChainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    (K.shiftFunctorObjXIso k n (n + k) rfl).inv ≫
        ((shiftFunctor (ChainComplex C ℤ) k).map f).f n =
      f.f (n + k) ≫ (L.shiftFunctorObjXIso k n (n + k) rfl).inv := sorry

namespace Shift.MinusOne

/-- The degree isomorphism for `K⟦-1⟧` at degree `n`. -/
@[stacks 011A "minus-one chain-shift degree isomorphism"]
abbrev xIso (K : ChainComplex C ℤ) (n : ℤ) :
    (K⟦(-1 : ℤ)⟧).X n ≅ K.X (n - 1) :=
  K.shiftFunctorObjXIso (-1) n (n - 1) (sub_eq_add_neg n 1)

/-- The degree isomorphism from `K⟦-1⟧` at `n + 1` to `K` at `n`. -/
abbrev succXIso (K : ChainComplex C ℤ) (n : ℤ) :
    (K⟦(-1 : ℤ)⟧).X (n + 1) ≅ K.X n :=
  xIso K (n + 1) ≪≫ K.XIsoOfEq (add_sub_cancel_right n 1)

/-- Shifting the natural degree `n + 1` down by one gives natural degree `n`. -/
theorem add_succNat_index (n : ℕ) :
    (-1 : ℤ) + ((Nat.succ n : ℕ) : ℤ) = (n : ℤ) := sorry

/-- The degree isomorphism from `K⟦-1⟧` at natural degree `n + 1` to `K` at natural degree
`n`. -/
@[stacks 011A "minus-one chain shift in a successor natural degree"]
def succNatXIso (K : ChainComplex C ℤ) (n : ℕ) :
    (K⟦(-1 : ℤ)⟧).X ((Nat.succ n : ℕ) : ℤ) ≅ K.X (n : ℤ) :=
  K.shiftFunctorObjXIso (-1) ((Nat.succ n : ℕ) : ℤ) (n : ℤ) <|
    (add_succNat_index n).symm.trans (add_comm (-1) ((Nat.succ n : ℕ) : ℤ))

/-- Under the standard degree identifications, the differential on `K⟦-1⟧` is the negative
of the translated differential on `K`. -/
theorem differential (K : ChainComplex C ℤ) (i j : ℤ) :
    (K⟦(-1 : ℤ)⟧).d i j =
      (xIso K i).hom ≫ (-K.d (i - 1) (j - 1)) ≫
        (xIso K j).inv := sorry

end Shift.MinusOne

end

end ChainComplex
