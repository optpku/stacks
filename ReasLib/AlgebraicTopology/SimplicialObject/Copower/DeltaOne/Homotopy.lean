module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.DeltaOne.Endpoint
public import ReasLib.CategoryTheory.Functor.IndexedCoproduct.HomFamily
public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Homotopy

/-!
@stack 019K

# Cylinder homotopies for the simplicial-interval copower

This module packages maps out of the simplicial cylinder with their endpoint laws and identifies
them with the canonical combinatorial simplicial homotopies.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject.copower.deltaOne

variable {C : Type u} [Category.{v} C]
/-- A homotopy presented by a morphism out of the simplicial cylinder
`copower Δ[1] X`, together with its two endpoint equations. -/
@[stacks 019K "simplicial cylinder homotopy"]
structure Homotopy {X Y : SimplicialObject C} (a b : X ⟶ Y)
    [HasCopower (Δ[1] : SSet.{w}) X] where
  /-- The morphism from the simplicial cylinder to the target. -/
  hom : SimplicialObject.copower (Δ[1] : SSet.{w}) X ⟶ Y
  /-- Restriction to the zero endpoint is `a`. -/
  zero : endpointZero X ≫ hom = a
  /-- Restriction to the one endpoint is `b`. -/
  one : endpointOne X ≫ hom = b

namespace Homotopy

variable {X Y : SimplicialObject C} {a b : X ⟶ Y}
variable [HasCopower (Δ[1] : SSet.{w}) X]

/-- The degree-`n`, index-`i` combinatorial component extracted from a cylinder homotopy. -/
@[stacks 019L "component of a simplicial cylinder homotopy"]
def component (H : Homotopy a b) {n : ℕ} (i : Fin (n + 1)) :
    X.obj (op ⦋n⦌) ⟶ Y.obj (op ⦋n + 1⦌) :=
  X.σ i ≫
    Functor.indexedCoprod.HomFamily.ofHom H.hom (op ⦋n + 1⦌)
      (SSet.stdSimplex.objMk₁ i.succ.castSucc)

/-- The initial face of `component` is the one endpoint of the cylinder homotopy. -/
@[stacks 019L "initial face of a simplicial homotopy component"]
theorem component.zero (H : Homotopy a b) (n : ℕ) :
    H.component (0 : Fin (n + 1)) ≫ Y.δ (0 : Fin (n + 2)) =
      b.app (op ⦋n⦌) := sorry

/-- The final face of `component` is the zero endpoint of the cylinder homotopy. -/
@[stacks 019L "final face of a simplicial homotopy component"]
theorem component.last (H : Homotopy a b) (n : ℕ) :
    H.component (Fin.last n) ≫ Y.δ (Fin.last (n + 1)) =
      a.app (op ⦋n⦌) := sorry

/-- A face before the homotopy index commutes with the extracted component. -/
@[stacks 019L "face before a simplicial homotopy index"]
theorem component.face_before (H : Homotopy a b) {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    H.component j.succ ≫ Y.δ i.castSucc = X.δ i ≫ H.component j := sorry

/-- The two adjacent face formulas for the extracted component agree. -/
@[stacks 019L "adjacent faces of a simplicial homotopy component"]
theorem component.face_adjacent (H : Homotopy a b) {n : ℕ}
    (j : Fin (n + 1)) :
    H.component j.succ ≫ Y.δ j.castSucc.succ =
      H.component j.castSucc ≫ Y.δ j.castSucc.succ := sorry

/-- A face after the homotopy index commutes with the extracted component. -/
@[stacks 019L "face after a simplicial homotopy index"]
theorem component.face_after (H : Homotopy a b) {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    H.component j.castSucc ≫ Y.δ i.succ = X.δ i ≫ H.component j := sorry

/-- A degeneracy before the homotopy index commutes with the extracted component. -/
@[stacks 019L "degeneracy before a simplicial homotopy index"]
theorem component.degeneracy_before (H : Homotopy a b) {n : ℕ}
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    H.component j ≫ Y.σ i.castSucc = X.σ i ≫ H.component j.succ := sorry

/-- A degeneracy after the homotopy index commutes with the extracted component. -/
@[stacks 019L "degeneracy after a simplicial homotopy index"]
theorem component.degeneracy_after (H : Homotopy a b) {n : ℕ}
    (i j : Fin (n + 1)) (hji : j ≤ i) :
    H.component j ≫ Y.σ i.succ = X.σ i ≫ H.component j.castSucc := sorry

/-- Convert a cylinder morphism with its endpoint equations to mathlib's canonical
combinatorial simplicial homotopy. -/
@[stacks 019L "cylinder-to-combinatorial homotopy"]
def toCombinatorial (H : Homotopy a b) : SimplicialObject.Homotopy a b where
  h i := H.component i
  h_zero_comp_δ_zero := component.zero H
  h_last_comp_δ_last := component.last H
  h_succ_comp_δ_castSucc_of_lt := component.face_before H
  h_succ_comp_δ_castSucc_succ := component.face_adjacent H
  h_castSucc_comp_δ_succ_of_lt := component.face_after H
  h_comp_σ_castSucc_of_le := component.degeneracy_before H
  h_comp_σ_succ_of_lt := component.degeneracy_after H

/-- The compatible cylinder family reconstructed from a combinatorial homotopy, evaluated at
a simplex of `Δ[1]`. -/
@[stacks 019L "combinatorial homotopy cylinder family"]
noncomputable def ofCombinatorial.family (H : SimplicialObject.Homotopy a b)
    (n : SimplexCategory) (i : (Δ[1] : SSet.{w}).obj (op n)) :
    X.obj (op n) ⟶ Y.obj (op n) :=
  match n with
  | .mk 0 =>
      SSet.stdSimplex.objMk₁Cases
        (a.app (op ⦋0⦌)) (b.app (op ⦋0⦌))
        (fun j : Fin 0 ↦ Fin.elim0 j) i
  | .mk (m + 1) =>
      SSet.stdSimplex.objMk₁Cases
        (a.app (op ⦋m + 1⦌)) (b.app (op ⦋m + 1⦌))
        (fun l ↦ X.δ (n := m) l.castSucc ≫ H.h (n := m) l) i

namespace ofCombinatorial.family

/-- The constant-zero simplex selects the zero endpoint of the reconstructed cylinder family. -/
@[simp, stacks 019L "zero endpoint of the reconstructed cylinder family"]
theorem zero (H : SimplicialObject.Homotopy a b) (n : ℕ) :
    ofCombinatorial.family H ⦋n⦌
        (SSet.stdSimplex.objMk₁ (Fin.last (n + 1))) =
      a.app (op ⦋n⦌) := sorry

/-- The constant-one simplex selects the one endpoint of the reconstructed cylinder family. -/
@[simp, stacks 019L "one endpoint of the reconstructed cylinder family"]
theorem one (H : SimplicialObject.Homotopy a b) (n : ℕ) :
    ofCombinatorial.family H ⦋n⦌
        (SSet.stdSimplex.objMk₁ (0 : Fin (n + 2))) =
      b.app (op ⦋n⦌) := sorry

/-- An interior simplex selects the corresponding face followed by the combinatorial homotopy
component. -/
@[simp, stacks 019L "interior component of the reconstructed cylinder family"]
theorem interior (H : SimplicialObject.Homotopy a b) {n : ℕ} (i : Fin (n + 1)) :
    ofCombinatorial.family H ⦋n + 1⦌
        (SSet.stdSimplex.objMk₁ i.succ.castSucc) =
      X.δ i.castSucc ≫ H.h i := sorry

end ofCombinatorial.family

/-- The reconstructed components as a simplex-indexed copower Hom family. -/
@[stacks 019L "combinatorial homotopy Hom family"]
noncomputable def ofCombinatorial.homFamily (H : SimplicialObject.Homotopy a b) :
    Functor.indexedCoprod.HomFamily (Δ[1] : SSet.{w}) X Y :=
  fun Δ i ↦ ofCombinatorial.family H Δ.unop i

/-- Evaluation of the reconstructed Hom family is the corresponding standard-simplex
component. -/
@[simp, stacks 019L "reconstructed cylinder Hom-family formula"]
theorem ofCombinatorial.homFamily.apply (H : SimplicialObject.Homotopy a b)
    (Δ : SimplexCategoryᵒᵖ) (i : (Δ[1] : SSet.{w}).obj Δ) :
    ofCombinatorial.homFamily H Δ i = ofCombinatorial.family H Δ.unop i := sorry

/-- The reconstructed cylinder family satisfies simplicial compatibility. -/
@[stacks 019L "compatibility of the reconstructed cylinder family"]
theorem ofCombinatorial.homFamily.isCompatible (H : SimplicialObject.Homotopy a b) :
    (ofCombinatorial.homFamily H).IsCompatible := sorry

/-- The compatible-family package reconstructed from a combinatorial homotopy. -/
@[stacks 019L "compatible combinatorial homotopy cylinder family"]
noncomputable def ofCombinatorial.compatible (H : SimplicialObject.Homotopy a b) :
    Functor.indexedCoprod.HomFamily.Compatible (Δ[1] : SSet.{w}) X Y :=
  ⟨ofCombinatorial.homFamily H, ofCombinatorial.homFamily.isCompatible H⟩

/-- The cylinder map assembled from a combinatorial homotopy restricts to its zero endpoint. -/
@[stacks 019L "zero endpoint law for the reconstructed cylinder map"]
theorem ofCombinatorial.zero (H : SimplicialObject.Homotopy a b) :
    endpointZero X ≫
        Functor.indexedCoprod.HomFamily.toHom (ofCombinatorial.compatible H) =
      a := sorry

/-- The cylinder map assembled from a combinatorial homotopy restricts to its one endpoint. -/
@[stacks 019L "one endpoint law for the reconstructed cylinder map"]
theorem ofCombinatorial.one (H : SimplicialObject.Homotopy a b) :
    endpointOne X ≫
        Functor.indexedCoprod.HomFamily.toHom (ofCombinatorial.compatible H) =
      b := sorry

/-- Assemble a canonical combinatorial homotopy into a cylinder morphism with endpoint laws. -/
@[stacks 019L "combinatorial-to-cylinder homotopy"]
noncomputable def ofCombinatorial (H : SimplicialObject.Homotopy a b) : Homotopy a b where
  hom := Functor.indexedCoprod.HomFamily.toHom (ofCombinatorial.compatible H)
  zero := ofCombinatorial.zero H
  one := ofCombinatorial.one H

namespace equiv

/-- Reconstructing a cylinder homotopy after extracting its components gives the original
cylinder homotopy. -/
@[stacks 019L "cylinder homotopy reconstruction inverse law"]
theorem left_inv (H : Homotopy a b) :
    ofCombinatorial H.toCombinatorial = H := sorry

/-- Extracting components after assembling a combinatorial homotopy gives the original
combinatorial homotopy. -/
@[stacks 019L "combinatorial homotopy reconstruction inverse law"]
theorem right_inv (H : SimplicialObject.Homotopy a b) :
    (ofCombinatorial H).toCombinatorial = H := sorry

end equiv

/-- Cylinder homotopies are canonically equivalent to mathlib's combinatorial homotopies. -/
@[stacks 019L "cylinder and combinatorial homotopy equivalence"]
noncomputable def equiv (a b : X ⟶ Y) : Homotopy a b ≃ SimplicialObject.Homotopy a b where
  toFun := toCombinatorial
  invFun := ofCombinatorial
  left_inv := equiv.left_inv
  right_inv := equiv.right_inv

/-- Applying the cylinder/combinatorial equivalence extracts the combinatorial components. -/
@[simp, stacks 019L "cylinder-to-combinatorial equivalence formula"]
theorem equiv.apply (H : Homotopy a b) :
    equiv a b H = H.toCombinatorial := sorry

/-- Applying the inverse cylinder/combinatorial equivalence reconstructs the cylinder map. -/
@[simp, stacks 019L "combinatorial-to-cylinder equivalence formula"]
theorem equiv.symm_apply (H : SimplicialObject.Homotopy a b) :
    (equiv a b).symm H = ofCombinatorial H := sorry

/-- Existence of a cylinder homotopy is equivalent to the canonical directed-homotopy
relation. -/
@[stacks 019K "directed cylinder homotopy bridge"]
theorem nonempty_iff (a b : X ⟶ Y) :
    Nonempty (Homotopy a b) ↔ SimplicialObject.DirectedHomotopy a b := sorry

/-- The zigzag relation generated by cylinder homotopies is the canonical simplicial-homotopy
relation. -/
@[stacks 019K "cylinder zigzag homotopy bridge"]
theorem homotopic_iff (a b : X ⟶ Y) :
    Relation.EqvGen (fun f g : X ⟶ Y ↦ Nonempty (Homotopy f g)) a b ↔
      SimplicialObject.Homotopic a b := sorry

end Homotopy

end CategoryTheory.SimplicialObject.copower.deltaOne
