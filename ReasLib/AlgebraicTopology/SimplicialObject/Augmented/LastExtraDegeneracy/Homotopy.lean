/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.LastExtraDegeneracy
public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyEquiv

/-!
# Simplicial contractions from last extra degeneracies

A last extra degeneracy supplies an explicit section of the augmentation.  Its defining face and
degeneracy relations make the augmentation-section composite simplicially homotopic to the
identity.  This file packages those two maps as the canonical ReasLib `HomotopyEquiv`; downstream
resolution constructions should specialize this owner rather than rebuild the equivalence.

@stack 08ND
-/

@[expose] public section

open CategoryTheory
open Opposite
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject.Augmented.LastExtraDegeneracy

variable {C : Type u} [Category.{v} C]
variable {X : SimplicialObject.Augmented C}

namespace homotopy

/-- The degree-`n`, vertex-`i` operator of the contraction induced by a last extra degeneracy.
It first removes the final vertices after `i`, applies the last extra degeneracy in degree `i`,
and then restores those final vertices. -/
@[stacks 08ND "homotopy operator from a last extra degeneracy"]
def h (ed : LastExtraDegeneracy X) {n : ℕ} (i : Fin (n + 1)) :
    X.left _⦋n⦌ ⟶ X.left _⦋n + 1⦌ :=
  X.left.δLastIter i.rev.val i.add_rev_cast ≫ ed.s i.val ≫
    X.left.σLastIter i.succ.rev.val i.succ.add_rev_cast

/-- At the initial vertex, the homotopy operator followed by the initial face is the
augmentation-section composite. -/
@[stacks 08ND "initial face law for the last-extra-degeneracy homotopy"]
theorem h_zero_comp_δ_zero (ed : LastExtraDegeneracy X) (n : ℕ) :
    h ed (0 : Fin (n + 1)) ≫ X.left.δ 0 =
      (X.hom ≫ ed.section_).app (op ⦋n⦌) := sorry

/-- At the final vertex, the homotopy operator followed by the final face is the identity. -/
@[stacks 08ND "final face law for the last-extra-degeneracy homotopy"]
theorem h_last_comp_δ_last (ed : LastExtraDegeneracy X) (n : ℕ) :
    h ed (Fin.last n) ≫ X.left.δ (Fin.last (n + 1)) =
      𝟙 _ := sorry

/-- A successor-indexed homotopy operator commutes with an earlier face. -/
@[stacks 08ND "earlier-face law for the last-extra-degeneracy homotopy"]
theorem h_succ_comp_δ_castSucc_of_lt (ed : LastExtraDegeneracy X) {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    h ed j.succ ≫ X.left.δ i.castSucc = X.left.δ i ≫ h ed j := sorry

/-- The two adjacent homotopy operators agree after the face between their indices. -/
@[stacks 08ND "adjacent-face law for the last-extra-degeneracy homotopy"]
theorem h_succ_comp_δ_castSucc_succ (ed : LastExtraDegeneracy X) {n : ℕ}
    (j : Fin (n + 1)) :
    h ed j.succ ≫ X.left.δ j.castSucc.succ =
      h ed j.castSucc ≫ X.left.δ j.castSucc.succ := sorry

/-- A cast-successor-indexed homotopy operator commutes with a later face. -/
@[stacks 08ND "later-face law for the last-extra-degeneracy homotopy"]
theorem h_castSucc_comp_δ_succ_of_lt (ed : LastExtraDegeneracy X) {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    h ed j.castSucc ≫ X.left.δ i.succ = X.left.δ i ≫ h ed j := sorry

/-- A homotopy operator commutes with a degeneracy whose index is at most its own index. -/
@[stacks 08ND "earlier-codegeneracy law for the last-extra-degeneracy homotopy"]
theorem h_comp_σ_castSucc_of_le (ed : LastExtraDegeneracy X) {n : ℕ}
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    h ed j ≫ X.left.σ i.castSucc = X.left.σ i ≫ h ed j.succ := sorry

/-- A homotopy operator commutes with a degeneracy whose index is at least its own index. -/
@[stacks 08ND "later-codegeneracy law for the last-extra-degeneracy homotopy"]
theorem h_comp_σ_succ_of_lt (ed : LastExtraDegeneracy X) {n : ℕ}
    (i j : Fin (n + 1)) (hji : j ≤ i) :
    h ed j ≫ X.left.σ i.succ = X.left.σ i ≫ h ed j.castSucc := sorry

end homotopy

/-- The concrete contraction from the identity to the augmentation-section composite supplied
by a last extra degeneracy. -/
@[stacks 08ND "simplicial homotopy from a last extra degeneracy"]
def homotopy (ed : LastExtraDegeneracy X) :
    SimplicialObject.Homotopy (𝟙 X.left) (X.hom ≫ ed.section_) where
  h := homotopy.h ed
  h_zero_comp_δ_zero := homotopy.h_zero_comp_δ_zero ed
  h_last_comp_δ_last := homotopy.h_last_comp_δ_last ed
  h_succ_comp_δ_castSucc_of_lt := homotopy.h_succ_comp_δ_castSucc_of_lt ed
  h_succ_comp_δ_castSucc_succ := homotopy.h_succ_comp_δ_castSucc_succ ed
  h_castSucc_comp_δ_succ_of_lt := homotopy.h_castSucc_comp_δ_succ_of_lt ed
  h_comp_σ_castSucc_of_le := homotopy.h_comp_σ_castSucc_of_le ed
  h_comp_σ_succ_of_lt := homotopy.h_comp_σ_succ_of_lt ed

/-- The components of the contraction are the explicit iterated-final-face operators. -/
@[simp, stacks 08ND "components of the last-extra-degeneracy homotopy"]
theorem homotopy_h (ed : LastExtraDegeneracy X) {n : ℕ} (i : Fin (n + 1)) :
    ed.homotopy.h i = homotopy.h ed i := sorry

/-- The augmentation followed by the section supplied by a last extra degeneracy is simplicially
homotopic to the identity, by reversing the concrete contraction `ed.homotopy`. -/
@[stacks 08ND "augmentation-section homotopy from a last extra degeneracy"]
theorem simplicialHomotopyEquiv.hom_inv_id (ed : LastExtraDegeneracy X) :
    SimplicialObject.Homotopic (X.hom ≫ ed.section_) (𝟙 X.left) := sorry

/-- The section supplied by a last extra degeneracy followed by the augmentation is simplicially
homotopic to the identity; this composite is already strictly the identity. -/
@[stacks 08ND "section-augmentation homotopy from a last extra degeneracy"]
theorem simplicialHomotopyEquiv.inv_hom_id (ed : LastExtraDegeneracy X) :
    SimplicialObject.Homotopic
      (ed.section_ ≫ X.hom) (𝟙 ((SimplicialObject.const C).obj X.right)) := sorry

/-- A last extra degeneracy packages its augmentation and canonical section as a simplicial
homotopy equivalence. -/
@[stacks 08ND "simplicial homotopy equivalence from a last extra degeneracy"]
def simplicialHomotopyEquiv (ed : LastExtraDegeneracy X) :
    SimplicialObject.HomotopyEquiv X.left
      ((SimplicialObject.const C).obj X.right) where
  hom := X.hom
  inv := ed.section_
  hom_inv_id := simplicialHomotopyEquiv.hom_inv_id ed
  inv_hom_id := simplicialHomotopyEquiv.inv_hom_id ed

/-- The forward map of the simplicial homotopy equivalence supplied by a last extra degeneracy is
the augmentation. -/
@[simp, stacks 08ND "forward map from a last extra degeneracy"]
theorem simplicialHomotopyEquiv.hom (ed : LastExtraDegeneracy X) :
    ed.simplicialHomotopyEquiv.hom = X.hom := sorry

/-- The inverse map of the simplicial homotopy equivalence supplied by a last extra degeneracy is
its canonical section. -/
@[simp, stacks 08ND "inverse map from a last extra degeneracy"]
theorem simplicialHomotopyEquiv.inv (ed : LastExtraDegeneracy X) :
    ed.simplicialHomotopyEquiv.inv = ed.section_ := sorry

/-- The inverse supplied by a last extra degeneracy is generated by its degree-zero section. -/
@[simp, stacks 08ND "inverse from a last extra degeneracy in degree zero"]
theorem simplicialHomotopyEquiv.inv_eq_fromZero (ed : LastExtraDegeneracy X) :
    ed.simplicialHomotopyEquiv.inv = X.left.fromZero ed.s' := sorry

/-- The augmentation of an augmented simplicial object with a last extra degeneracy is a
simplicial homotopy equivalence. -/
@[stacks 08ND "augmentation with a last extra degeneracy is a homotopy equivalence"]
theorem isHomotopyEquivalence (ed : LastExtraDegeneracy X) :
    SimplicialObject.IsHomotopyEquivalence X.hom := sorry

end CategoryTheory.SimplicialObject.Augmented.LastExtraDegeneracy
