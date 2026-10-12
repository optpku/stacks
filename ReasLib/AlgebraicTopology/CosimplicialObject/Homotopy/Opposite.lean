/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.Equiv
public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyEquiv
public import ReasLib.AlgebraicTopology.SimplicialSet.DeltaOne.Endpoint
public import ReasLib.AlgebraicTopology.SimplicialSet.StdSimplexOne
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 019X

# Opposite simplicial presentation of cosimplicial homotopy

This module compares the product-free `Δ[1]` presentation of cosimplicial homotopy with
the combinatorial simplicial homotopy of opposite simplicial objects.  It intentionally owns
only this variance bridge; Čech-conerve and cochain-complex applications belong in their own
modules.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial

noncomputable section

universe u v u' v'

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]
variable {U V : CosimplicialObject C} {a b : U ⟶ V}

namespace DeltaOneHomotopy

namespace opposite

/-- The `i`th simplicial-homotopy component induced by a product-free `Δ[1]`-homotopy. -/
@[stacks 019X "opposite homotopy component"]
def component (H : DeltaOneHomotopy a b) {n : ℕ} (i : Fin (n + 1)) :=
  (H.hom (SSet.stdSimplex.objMk₁ i.succ.castSucc) ≫ V.map (SimplexCategory.σ i)).op

/-- The defining formula for the component of the induced opposite simplicial homotopy. -/
@[simp, stacks 019X "opposite homotopy component formula"] theorem component.apply (H : DeltaOneHomotopy a b)
    {n : ℕ} (i : Fin (n + 1)) :
    component H i =
      (H.hom (SSet.stdSimplex.objMk₁ i.succ.castSucc) ≫ V.map (SimplexCategory.σ i)).op := sorry

namespace component

namespace face

/-- The zero-face endpoint identity for `component`. -/
@[stacks 019X "opposite homotopy zero endpoint law"]
theorem zero_comp (H : DeltaOneHomotopy a b) (n : ℕ) :
    component H 0 ≫ SimplicialObject.δ U.op 0 = (NatTrans.op b).app (op ⦋n⦌) := sorry

/-- The last-face endpoint identity for `component`. -/
@[stacks 019X "opposite homotopy last endpoint law"]
theorem last_comp (H : DeltaOneHomotopy a b) (n : ℕ) :
    component H (Fin.last n) ≫ SimplicialObject.δ U.op (Fin.last (n + 1)) =
      (NatTrans.op a).app (op ⦋n⦌) := sorry

/-- The first interior coface identity for `component`. -/
@[stacks 019X "opposite homotopy coface law one"]
theorem succ_comp_castSucc_of_lt (H : DeltaOneHomotopy a b)
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    component H j.succ ≫ SimplicialObject.δ U.op i.castSucc =
      SimplicialObject.δ V.op i ≫ component H j := sorry

/-- The adjacent coface identity for `component`. -/
@[stacks 019X "opposite homotopy adjacent coface law"]
theorem succ_comp_castSucc_succ (H : DeltaOneHomotopy a b)
    {n : ℕ} (j : Fin (n + 1)) :
    component H j.succ ≫ SimplicialObject.δ U.op j.castSucc.succ =
      component H j.castSucc ≫ SimplicialObject.δ U.op j.castSucc.succ := sorry

/-- The second interior coface identity for `component`. -/
@[stacks 019X "opposite homotopy coface law two"]
theorem castSucc_comp_succ_of_lt (H : DeltaOneHomotopy a b)
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    component H j.castSucc ≫ SimplicialObject.δ U.op i.succ =
      SimplicialObject.δ V.op i ≫ component H j := sorry

end face

namespace degeneracy

/-- The first codegeneracy identity for `component`. -/
@[stacks 019X "opposite homotopy codegeneracy law one"]
theorem comp_castSucc_of_le (H : DeltaOneHomotopy a b)
    {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    component H j ≫ SimplicialObject.σ U.op i.castSucc =
      SimplicialObject.σ V.op i ≫ component H j.succ := sorry

/-- The second codegeneracy identity for `component`. -/
@[stacks 019X "opposite homotopy codegeneracy law two"]
theorem comp_succ_of_lt (H : DeltaOneHomotopy a b)
    {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    component H j ≫ SimplicialObject.σ U.op i.succ =
      SimplicialObject.σ V.op i ≫ component H j.castSucc := sorry

end degeneracy

end component

/-- Convert a product-free cosimplicial `Δ[1]`-homotopy into a simplicial homotopy between
the opposite morphisms. -/
@[stacks 019X "opposite simplicial homotopy bridge"]
def toSimplicial (H : DeltaOneHomotopy a b) :
    SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b) where
  h i := component H i
  h_zero_comp_δ_zero := component.face.zero_comp H
  h_last_comp_δ_last := component.face.last_comp H
  h_succ_comp_δ_castSucc_of_lt := component.face.succ_comp_castSucc_of_lt H
  h_succ_comp_δ_castSucc_succ := component.face.succ_comp_castSucc_succ H
  h_castSucc_comp_δ_succ_of_lt := component.face.castSucc_comp_succ_of_lt H
  h_comp_σ_castSucc_of_le := component.degeneracy.comp_castSucc_of_le H
  h_comp_σ_succ_of_lt := component.degeneracy.comp_succ_of_lt H

/-- The component of `toSimplicial` is `component`. -/
@[simp, stacks 019X "opposite homotopy forward component"] theorem toSimplicial.h (H : DeltaOneHomotopy a b)
    {n : ℕ} (i : Fin (n + 1)) :
    (toSimplicial H).h i = component H i := sorry

/-- The degreewise cosimplicial component reconstructed from an arbitrary simplicial homotopy
valued in an opposite category. -/
@[stacks 019X "reconstructed opposite homotopy component"]
noncomputable def unopComponent
    {X' Y' : SimplicialObject Cᵒᵖ} {f g : X' ⟶ Y'}
    (H : SimplicialObject.Homotopy f g)
    {n : SimplexCategory} (i : (Δ[1] : SSet.{0}).obj (op n)) :
    Y'.unop.obj n ⟶ X'.unop.obj n :=
  match n with
  | .mk 0 =>
      SSet.stdSimplex.objMk₁Cases
        ((NatTrans.unop f).app ⦋0⦌) ((NatTrans.unop g).app ⦋0⦌)
        (fun j : Fin 0 ↦ Fin.elim0 j) i
  | .mk (m + 1) =>
      SSet.stdSimplex.objMk₁Cases
        ((NatTrans.unop f).app ⦋m + 1⦌) ((NatTrans.unop g).app ⦋m + 1⦌)
        (fun l ↦ (H.h l).unop ≫ CosimplicialObject.δ X'.unop l.castSucc) i

namespace unopComponent

/-- The reconstructed component at the constant `0` simplex is the first endpoint. -/
@[simp, stacks 019X "zero endpoint of the reconstructed opposite homotopy component"]
theorem zero_endpoint
    {X' Y' : SimplicialObject Cᵒᵖ} {f g : X' ⟶ Y'}
    (H : SimplicialObject.Homotopy f g) (n : SimplexCategory) :
    unopComponent H (SSet.deltaOne.endpoint 0 (op n)) =
      (NatTrans.unop f).app n := sorry

/-- The reconstructed component at the constant `1` simplex is the second endpoint. -/
@[simp, stacks 019X "one endpoint of the reconstructed opposite homotopy component"]
theorem one_endpoint
    {X' Y' : SimplicialObject Cᵒᵖ} {f g : X' ⟶ Y'}
    (H : SimplicialObject.Homotopy f g) (n : SimplexCategory) :
    unopComponent H (SSet.deltaOne.endpoint 1 (op n)) =
      (NatTrans.unop g).app n := sorry

/-- An interior simplex selects the corresponding homotopy component followed by the
relevant coface of the unopposite cosimplicial object. -/
@[simp, stacks 019X "interior reconstructed opposite homotopy component"]
theorem interior
    {X' Y' : SimplicialObject Cᵒᵖ} {f g : X' ⟶ Y'}
    (H : SimplicialObject.Homotopy f g) {n : ℕ} (i : Fin (n + 1)) :
    unopComponent H (SSet.stdSimplex.objMk₁ i.succ.castSucc) =
      (H.h i).unop ≫ CosimplicialObject.δ X'.unop i.castSucc := sorry

/-- The reconstructed component family is natural for every simplex operator. -/
@[stacks 019X "naturality of reconstructed opposite homotopy component"]
theorem naturality
    {X' Y' : SimplicialObject Cᵒᵖ} {f g : X' ⟶ Y'}
    (H : SimplicialObject.Homotopy f g)
    {n₁ n₂ : SimplexCategory} (σ : n₁ ⟶ n₂)
    (i : (Δ[1] : SSet).obj (op n₂)) :
    CommSq (Y'.unop.map σ)
      (unopComponent H ((Δ[1] : SSet).map σ.op i))
      (unopComponent H i) (X'.unop.map σ) := sorry

end unopComponent

/-- Convert a simplicial homotopy between opposite morphisms into a product-free cosimplicial
`Δ[1]`-homotopy. -/
@[stacks 019X "reconstructed cosimplicial homotopy bridge"]
noncomputable def ofSimplicial
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b)) : DeltaOneHomotopy a b where
  hom i := unopComponent H i
  zero_endpoint := unopComponent.zero_endpoint H
  one_endpoint := unopComponent.one_endpoint H
  naturality := unopComponent.naturality H

/-- The component of `ofSimplicial` is the explicit `unopComponent` formula. -/
@[simp, stacks 019X "reconstructed homotopy component formula"] theorem ofSimplicial.hom
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b))
    {n : SimplexCategory} (i : (Δ[1] : SSet).obj (op n)) :
    (ofSimplicial H).hom i = unopComponent H i := sorry

namespace equiv

/-- Reconstructing a product-free homotopy after passing to opposite simplicial objects is the
original homotopy. -/
@[stacks 019X "opposite homotopy left inverse"]
theorem left_inv (H : DeltaOneHomotopy a b) :
    ofSimplicial (toSimplicial H) = H := sorry

/-- Passing to the opposite simplicial homotopy after reconstruction is the original simplicial
homotopy. -/
@[stacks 019X "opposite homotopy right inverse"]
theorem right_inv
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b)) :
    toSimplicial (ofSimplicial H) = H := sorry

end equiv

/-- Lemma 14.28.3: product-free cosimplicial `Δ[1]`-homotopies are equivalent to simplicial
homotopies of the corresponding opposite morphisms. -/
@[stacks 019X "opposite simplicial homotopy equivalence"]
noncomputable def equiv (a b : U ⟶ V) :
    DeltaOneHomotopy a b ≃ SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b) where
  toFun := fun H ↦ toSimplicial H
  invFun := fun H ↦ ofSimplicial H
  left_inv := fun H ↦ equiv.left_inv H
  right_inv := fun H ↦ equiv.right_inv H

/-- The forward map of the opposite-homotopy equivalence is `toSimplicial`. -/
@[simp, stacks 019X "forward opposite simplicial homotopy equivalence"]
theorem equiv.apply (H : DeltaOneHomotopy a b) :
    equiv a b H = toSimplicial H := sorry

/-- The inverse map of the opposite-homotopy equivalence is `ofSimplicial`. -/
@[simp, stacks 019X "inverse opposite simplicial homotopy equivalence"]
theorem equiv.symm_apply
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b)) :
    (equiv a b).symm H = ofSimplicial H := sorry

end opposite

end DeltaOneHomotopy

/-- Passage to opposite simplicial objects preserves the zigzag relation generated by
product-free `Δ[1]`-homotopies. -/
@[stacks 019X "product-free homotopy passes to opposite simplicial objects"]
theorem DeltaOneHomotopic.opposite
    (h : DeltaOneHomotopic a b) :
    SimplicialObject.Homotopic (NatTrans.op a) (NatTrans.op b) := sorry

/-- The product-free cosimplicial and opposite-simplicial zigzag homotopy relations agree. -/
@[stacks 019X "opposite simplicial homotopy relation"]
theorem DeltaOneHomotopic.iff_op (a b : U ⟶ V) :
    DeltaOneHomotopic a b ↔
      SimplicialObject.Homotopic (NatTrans.op a) (NatTrans.op b) := sorry

namespace DeltaOneHomotopic

/-- A contravariant functor sends product-free cosimplicial homotopies to simplicial homotopies
of the induced opposite images. -/
@[stacks 019Y "contravariant opposite homotopy map"]
theorem contravariantMap (h : DeltaOneHomotopic a b) (F : Cᵒᵖ ⥤ D) :
    SimplicialObject.Homotopic
      (Functor.whiskerRight (NatTrans.op a) F)
      (Functor.whiskerRight (NatTrans.op b) F) := sorry

end DeltaOneHomotopic

namespace HomotopyEquiv

namespace opposite

/-- The opposite of the first homotopy identity of a cosimplicial homotopy equivalence. -/
@[stacks 019Y "opposite homotopy equivalence"]
theorem hom_inv (e : HomotopyEquiv U V) :
    SimplicialObject.Homotopic
      (NatTrans.op e.hom ≫ NatTrans.op e.inv) (𝟙 V.op) := sorry

/-- The opposite of the second homotopy identity of a cosimplicial homotopy equivalence. -/
@[stacks 019Y "opposite homotopy equivalence"]
theorem inv_hom (e : HomotopyEquiv U V) :
    SimplicialObject.Homotopic
      (NatTrans.op e.inv ≫ NatTrans.op e.hom) (𝟙 U.op) := sorry

/-- A cosimplicial homotopy equivalence gives a simplicial homotopy equivalence between the
opposite objects. -/
@[stacks 019Y "opposite homotopy equivalence"]
def toSimplicial (e : HomotopyEquiv U V) :
    SimplicialObject.HomotopyEquiv V.op U.op where
  hom := NatTrans.op e.hom
  inv := NatTrans.op e.inv
  hom_inv_id := hom_inv e
  inv_hom_id := inv_hom e

/-- The forward morphism of the opposite simplicial homotopy equivalence is the opposite of the
original forward morphism. -/
@[simp, stacks 019Y "forward morphism of an opposite homotopy equivalence"]
theorem toSimplicial.hom (e : HomotopyEquiv U V) :
    (toSimplicial e).hom = NatTrans.op e.hom := sorry

/-- The inverse morphism of the opposite simplicial homotopy equivalence is the opposite of the
original inverse morphism. -/
@[simp, stacks 019Y "inverse morphism of an opposite homotopy equivalence"]
theorem toSimplicial.inv (e : HomotopyEquiv U V) :
    (toSimplicial e).inv = NatTrans.op e.inv := sorry

/-- The first homotopy identity recovered from an opposite simplicial homotopy equivalence. -/
@[stacks 019Y "recovered opposite homotopy equivalence first law"]
theorem of_hom_inv
    (e : SimplicialObject.HomotopyEquiv V.op U.op) :
    DeltaOneHomotopic
      (NatTrans.unop e.hom ≫ NatTrans.unop e.inv) (𝟙 U) := sorry

/-- The second homotopy identity recovered from an opposite simplicial homotopy equivalence. -/
@[stacks 019Y "recovered opposite homotopy equivalence second law"]
theorem of_inv_hom
    (e : SimplicialObject.HomotopyEquiv V.op U.op) :
    DeltaOneHomotopic
      (NatTrans.unop e.inv ≫ NatTrans.unop e.hom) (𝟙 V) := sorry

/-- An opposite simplicial homotopy equivalence gives a cosimplicial product-free homotopy
equivalence. -/
@[stacks 019Y "reconstructed homotopy equivalence"]
def ofSimplicial
    (e : SimplicialObject.HomotopyEquiv V.op U.op) : HomotopyEquiv U V where
  hom := NatTrans.unop e.hom
  inv := NatTrans.unop e.inv
  hom_inv_id := of_hom_inv e
  inv_hom_id := of_inv_hom e

/-- The forward morphism reconstructed from an opposite simplicial homotopy equivalence is its
unopposite forward morphism. -/
@[simp, stacks 019Y "forward morphism reconstructed from an opposite homotopy equivalence"]
theorem ofSimplicial.hom
    (e : SimplicialObject.HomotopyEquiv V.op U.op) :
    (ofSimplicial e).hom = NatTrans.unop e.hom := sorry

/-- The inverse morphism reconstructed from an opposite simplicial homotopy equivalence is its
unopposite inverse morphism. -/
@[simp, stacks 019Y "inverse morphism reconstructed from an opposite homotopy equivalence"]
theorem ofSimplicial.inv
    (e : SimplicialObject.HomotopyEquiv V.op U.op) :
    (ofSimplicial e).inv = NatTrans.unop e.inv := sorry

namespace equiv

/-- Reconstructing a cosimplicial homotopy equivalence after passing to opposite simplicial
objects recovers the original structured equivalence. -/
@[stacks 019Y "opposite homotopy equivalence reconstruction"]
theorem left_inv (e : HomotopyEquiv U V) :
    ofSimplicial (toSimplicial e) = e := sorry

/-- Passing a reconstructed homotopy equivalence back to opposite simplicial objects recovers
the original structured equivalence. -/
@[stacks 019Y "opposite homotopy equivalence reconstruction"]
theorem right_inv (e : SimplicialObject.HomotopyEquiv V.op U.op) :
    toSimplicial (ofSimplicial e) = e := sorry

end equiv

/-- Cosimplicial homotopy equivalences are equivalent to simplicial homotopy equivalences
between the corresponding opposite objects. -/
@[stacks 019Y "bundled opposite homotopy equivalence"]
def equiv :
    HomotopyEquiv U V ≃ SimplicialObject.HomotopyEquiv V.op U.op where
  toFun := toSimplicial
  invFun := ofSimplicial
  left_inv := equiv.left_inv
  right_inv := equiv.right_inv

/-- The forward map of the bundled opposite homotopy-equivalence comparison is
`toSimplicial`. -/
@[simp, stacks 019Y "forward bundled opposite homotopy equivalence"]
theorem equiv.apply (e : HomotopyEquiv U V) :
    equiv e = toSimplicial e := sorry

/-- The inverse map of the bundled opposite homotopy-equivalence comparison is
`ofSimplicial`. -/
@[simp, stacks 019Y "inverse bundled opposite homotopy equivalence"]
theorem equiv.symm_apply (e : SimplicialObject.HomotopyEquiv V.op U.op) :
    equiv.symm e = ofSimplicial e := sorry

end opposite

end HomotopyEquiv

/-- A morphism of cosimplicial objects is a product-free homotopy equivalence exactly when its
opposite simplicial morphism is a simplicial homotopy equivalence. -/
@[stacks 019Y "opposite homotopy equivalence criterion"]
theorem IsHomotopyEquivalence.iff_op (a : U ⟶ V) :
    IsHomotopyEquivalence a ↔ SimplicialObject.IsHomotopyEquivalence (NatTrans.op a) := sorry

end CategoryTheory.CosimplicialObject

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]
variable {X Y : SimplicialObject D} {f g : X ⟶ Y}

namespace Homotopy

variable {X' Y' : SimplicialObject Cᵒᵖ} {a b : X' ⟶ Y'}

/-- Unopposite a simplicial homotopy valued in an opposite category to obtain its canonical
product-free cosimplicial `Δ[1]`-homotopy. -/
@[stacks 019X "unopposite simplicial homotopy bridge"]
noncomputable def unop (H : SimplicialObject.Homotopy a b) :
    CosimplicialObject.DeltaOneHomotopy (NatTrans.unop a) (NatTrans.unop b) :=
  CosimplicialObject.DeltaOneHomotopy.opposite.ofSimplicial H

/-- The components of the unopposed homotopy are given by the canonical reconstructed
`Δ[1]`-indexed family. -/
@[simp, stacks 019X "unopposite simplicial homotopy components"]
theorem unop.hom (H : SimplicialObject.Homotopy a b)
    {n : SimplexCategory} (i : (Δ[1] : SSet).obj (op n)) :
    (unop H).hom i =
      CosimplicialObject.DeltaOneHomotopy.opposite.unopComponent
        H i := sorry

end Homotopy

namespace Homotopic

variable {U' V' : CosimplicialObject C} {a b : U' ⟶ V'}

/-- Passage back from opposite simplicial objects preserves the zigzag relation generated by
combinatorial simplicial homotopies. -/
@[stacks 019X "opposite simplicial homotopy returns to cosimplicial objects"]
theorem unop
    (h : Homotopic (NatTrans.op a) (NatTrans.op b)) :
    CosimplicialObject.DeltaOneHomotopic a b := sorry

/-- A contravariant functor sends simplicial homotopies to product-free cosimplicial homotopies
of the induced opposite images. -/
@[stacks 019Y "contravariant simplicial homotopy map"]
theorem contravariantMap (h : Homotopic f g) (F : D ⥤ Cᵒᵖ) :
    CosimplicialObject.DeltaOneHomotopic
      (NatTrans.unop (Functor.whiskerRight f F))
      (NatTrans.unop (Functor.whiskerRight g F)) := sorry

end Homotopic

end CategoryTheory.SimplicialObject
