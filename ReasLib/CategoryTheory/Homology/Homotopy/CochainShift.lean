/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Homotopies and Shifts of Cochain Complexes

Self-homotopies of a cochain map are identified with maps into the `(-1)`-shifted target.  The
nonempty set of homotopies between two fixed maps is recorded as a principal homogeneous space.
-/

@[expose] public section

open CategoryTheory

universe v u

variable {ι : Type*} {c : ComplexShape ι}
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {K L : HomologicalComplex C c} {f g : K ⟶ L}

namespace Homotopy

/-- Transport both endpoints of a homotopy along equalities of morphisms. -/
def congrEquiv {f' g' : K ⟶ L} (hf : f = f') (hg : g = g') :
    Homotopy f g ≃ Homotopy f' g' :=
  Equiv.cast (congrArg₂ Homotopy hf hg)

/-- Translating a homotopy by a fixed reverse homotopy and then translating back is the
identity. -/
theorem translateEquivSelf_leftInverse (h : Homotopy f g) (k : Homotopy f g) :
    (k.trans h.symm).trans h = k := sorry

/-- Translating a self-homotopy by a fixed homotopy and then by its reverse is the identity. -/
theorem translateEquivSelf_rightInverse (h : Homotopy f g) (k : Homotopy f f) :
    (k.trans h).trans h.symm = k := sorry

/-- A chosen homotopy from `f` to `g` identifies all such homotopies with self-homotopies of
`f`. -/
def translateEquivSelf (h : Homotopy f g) : Homotopy f g ≃ Homotopy f f where
  toFun k := k.trans h.symm
  invFun k := k.trans h
  left_inv := translateEquivSelf_leftInverse h
  right_inv := translateEquivSelf_rightInverse h

/-- Self-homotopies of a morphism are equivalent to homotopies from zero to zero. -/
def selfEquivZero (f : K ⟶ L) :
    Homotopy f f ≃ Homotopy (0 : K ⟶ L) (0 : K ⟶ L) :=
  equivSubZero.trans (congrEquiv (sub_self f) rfl)

/-- If self-homotopies of `f` are identified with `G`, then homotopies from `f` to `g` are
either empty or equivalent to `G`. -/
theorem isEmpty_or_nonempty_equiv {G : Type*} (f g : K ⟶ L)
    (e : Homotopy f f ≃ G) :
    IsEmpty (Homotopy f g) ∨ Nonempty (Homotopy f g ≃ G) := sorry

/-- If self-homotopies of `f` are identified with an additive group `G`, then the homotopies
from `f` to `g` are either empty or form a principal homogeneous space under `G`. -/
theorem isEmpty_or_nonempty_addTorsor {G : Type*} [AddGroup G] (f g : K ⟶ L)
    (e : Homotopy f f ≃ G) :
    IsEmpty (Homotopy f g) ∨ Nonempty (AddTorsor G (Homotopy f g)) := sorry

end Homotopy

namespace CochainComplex

namespace Homotopy

open HomComplex

noncomputable section

variable {A B : CochainComplex C ℤ}

/-- For a degree `-1` cochain, the zero-homotopy equation is exactly the cocycle condition. -/
theorem zeroCochain_iff (z : Cochain A B (-1)) :
    Cochain.ofHom (0 : A ⟶ B) = δ (-1) 0 z + Cochain.ofHom (0 : A ⟶ B) ↔
      z ∈ cocycle A B (-1) := sorry

/-- Homotopies from the zero cochain map to itself are canonically degree `-1` cocycles. -/
noncomputable def zeroEquivCocycle :
    Homotopy (0 : A ⟶ B) 0 ≃ Cocycle A B (-1) :=
  (Cochain.equivHomotopy (0 : A ⟶ B) 0).trans
    (Equiv.subtypeEquivRight zeroCochain_iff)

/-- Self-homotopies of a cochain map are canonically maps into the `(-1)`-shifted target. -/
@[stacks 011I]
noncomputable def selfEquivShiftHom (a : A ⟶ B) :
    Homotopy a a ≃ (A ⟶ B⟦(-1 : ℤ)⟧) :=
  (_root_.Homotopy.selfEquivZero a).trans
    (zeroEquivCocycle.trans Cocycle.equivHomShift.symm.toEquiv)

/-- Homotopies between two cochain maps are either empty or form a principal homogeneous space
under the group of maps into the `(-1)`-shifted target. -/
@[stacks 011I]
theorem isEmpty_or_nonempty_addTorsor (a b : A ⟶ B) :
    IsEmpty (Homotopy a b) ∨
      Nonempty (AddTorsor (A ⟶ B⟦(-1 : ℤ)⟧) (Homotopy a b)) := sorry

end

end Homotopy

end CochainComplex
