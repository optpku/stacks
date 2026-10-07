module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.WithTerminal.Cone
public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.KanExtension.FiniteInstances
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.Limit
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.StructureMaps
public import stacks_project.Chap92.Example_92_5_9_Terms
public import stacks_project.Chap92.Lemma_92_4_1_Evaluation

/-!
# Length-two simplicial polynomial diagrams

This leaf packages the explicit `P0`, `P1`, `P2` data of a presentation as truncated
simplicial objects in the slice `Over (CommAlgCat.of A B)`, together with the
`2`-coskeleton, matching map, and forgotten augmentation.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open CategoryTheory.SimplicialObject.Truncated
open Opposite
open Algebra
open Algebra.Presentation.LengthTwo
open MvPolynomial
open scoped Simplicial SimplexCategory.Truncated

universe u

namespace Algebra.Presentation.LengthTwo

variable {A B ι σ : Type u} [CommRing A] [CommRing B] [Algebra A B]

noncomputable section

/-- The truncation degree of a `1`-truncated simplex, as an element of `Fin 2`. -/
def deg1 (k : SimplexCategory.Truncated 1) : Fin 2 :=
  ⟨k.obj.len, Nat.lt_succ_of_le k.property⟩

/-- The truncation degree of a `2`-truncated simplex, as an element of `Fin 3`. -/
def deg2 (k : SimplexCategory.Truncated 2) : Fin 3 :=
  ⟨k.obj.len, Nat.lt_succ_of_le k.property⟩

/-- Degree of `deg1` recovers the simplex length. -/
theorem deg1_val (k : SimplexCategory.Truncated 1) : (deg1 k).val = k.obj.len :=
  sorry

/-- Degree of `deg2` recovers the simplex length. -/
theorem deg2_val (k : SimplexCategory.Truncated 2) : (deg2 k).val = k.obj.len :=
  sorry

/-- The `1`-truncated coefficient algebras `P0` and `P1`. -/
def alg1 (P : Presentation A B ι σ) : Fin 2 → CommAlgCat.{u} A
  | ⟨0, _⟩ => CommAlgCat.of A (term0 P)
  | ⟨1, _⟩ => CommAlgCat.of A (term1 P)
  | ⟨n + 2, h⟩ => nomatch h

/-- The `2`-truncated coefficient algebras `P0`, `P1`, and `P2`. -/
def alg2 (P : Presentation A B ι σ) : Fin 3 → CommAlgCat.{u} A
  | ⟨0, _⟩ => CommAlgCat.of A (term0 P)
  | ⟨1, _⟩ => CommAlgCat.of A (term1 P)
  | ⟨2, _⟩ => CommAlgCat.of A (term2 P)
  | ⟨n + 3, h⟩ => nomatch h

/-- The face `P1 → P0` selected by a coface `δ i : ⦋0⦌ ⟶ ⦋1⦌`. -/
def faceFromHom (P : Presentation A B ι σ) (φ : ⦋0⦌ ⟶ ⦋1⦌) : term1 P →ₐ[A] P.Ring :=
  if φ = SimplexCategory.δ 0 then faceZero P else faceOne P

/-- `δ 0` induces `d0` and `δ 1` induces `d1`. -/
theorem faceFromHom_δ (P : Presentation A B ι σ) (i : Fin 2) :
    faceFromHom P (SimplexCategory.δ i) = if i = 0 then faceZero P else faceOne P :=
  sorry

/-- Identity, `s0 ∘ d1`, or `s0 ∘ d0` according to a morphism `⦋1⦌ ⟶ ⦋1⦌`. -/
def term1End (P : Presentation A B ι σ) (φ : ⦋1⦌ ⟶ ⦋1⦌) : term1 P →ₐ[A] term1 P :=
  if φ = 𝟙 _ then AlgHom.id A (term1 P)
  else if φ = SimplexCategory.const ⦋1⦌ ⦋1⦌ 0 then (degeneracyZero P).comp (faceOne P)
  else (degeneracyZero P).comp (faceZero P)

/-- The identity morphism of `⦋1⦌` induces the identity on `P1`. -/
theorem term1End_id (P : Presentation A B ι σ) :
    term1End P (𝟙 _) = AlgHom.id A (term1 P) :=
  sorry

/-- The constant map onto `0` induces `s0 ∘ d1`. -/
theorem term1End_const_zero (P : Presentation A B ι σ) :
    term1End P (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0) =
      (degeneracyZero P).comp (faceOne P) :=
  sorry

/-- The algebra map `P2 → P1` induced by a morphism `⦋1⦌ ⟶ ⦋2⦌`, as a composite of
elementary faces and degeneracies. -/
def faceTwoFromHom (P : Presentation A B ι σ) (φ : ⦋1⦌ ⟶ ⦋2⦌) : term2 P →ₐ[A] term1 P :=
  if φ = SimplexCategory.δ 0 then faceTwo P 0
  else if φ = SimplexCategory.δ 1 then faceTwo P 1
  else if φ = SimplexCategory.δ 2 then faceTwo P 2
  else if φ = SimplexCategory.const ⦋1⦌ ⦋2⦌ 0 then
    (degeneracyZero P).comp ((faceOne P).comp (faceTwo P 2))
  else if φ = SimplexCategory.const ⦋1⦌ ⦋2⦌ 1 then
    (degeneracyZero P).comp ((faceZero P).comp (faceTwo P 2))
  else
    (degeneracyZero P).comp ((faceZero P).comp (faceTwo P 0))

/-- A coface `δ i : ⦋1⦌ ⟶ ⦋2⦌` induces the face `d_i : P2 → P1`. -/
theorem faceTwoFromHom_δ (P : Presentation A B ι σ) (i : Fin 3) :
    faceTwoFromHom P (SimplexCategory.δ i) = faceTwo P i :=
  sorry

/-- The constant map `⦋1⦌ ⟶ ⦋2⦌` onto `0` is `s0 ∘ d1 ∘ d2`. -/
theorem faceTwoFromHom_const_zero (P : Presentation A B ι σ) :
    faceTwoFromHom P (SimplexCategory.const ⦋1⦌ ⦋2⦌ 0) =
      (degeneracyZero P).comp ((faceOne P).comp (faceTwo P 2)) :=
  sorry

/-- The algebra map `P1 → P2` induced by a morphism `⦋2⦌ ⟶ ⦋1⦌`, as a composite of
elementary faces and degeneracies. -/
def degeneracyOneFromHom (P : Presentation A B ι σ) (φ : ⦋2⦌ ⟶ ⦋1⦌) :
    term1 P →ₐ[A] term2 P :=
  if φ = SimplexCategory.σ 0 then degeneracyOne P 0
  else if φ = SimplexCategory.σ 1 then degeneracyOne P 1
  else if φ = SimplexCategory.const ⦋2⦌ ⦋1⦌ 0 then (rename Vars.u).comp (faceOne P)
  else (rename Vars.u).comp (faceZero P)

/-- A codegeneracy `σ j : ⦋2⦌ ⟶ ⦋1⦌` induces `s_j : P1 → P2`. -/
theorem degeneracyOneFromHom_σ (P : Presentation A B ι σ) (j : Fin 2) :
    degeneracyOneFromHom P (SimplexCategory.σ j) = degeneracyOne P j :=
  sorry

/-- The constant map `⦋2⦌ ⟶ ⦋1⦌` onto `0` is `rename Vars.u ∘ d1`, not `s0`. -/
theorem degeneracyOneFromHom_const_zero (P : Presentation A B ι σ) :
    degeneracyOneFromHom P (SimplexCategory.const ⦋2⦌ ⦋1⦌ 0) =
      (rename Vars.u).comp (faceOne P) :=
  sorry

/-- Vertex maps `P2 → P0` selected by a morphism `⦋0⦌ ⟶ ⦋2⦌`. -/
def vertexFromHom (P : Presentation A B ι σ) (φ : ⦋0⦌ ⟶ ⦋2⦌) : term2 P →ₐ[A] P.Ring :=
  if φ = SimplexCategory.const ⦋0⦌ ⦋2⦌ 0 then (faceOne P).comp (faceTwo P 2)
  else if φ = SimplexCategory.const ⦋0⦌ ⦋2⦌ 1 then (faceZero P).comp (faceTwo P 2)
  else (faceZero P).comp (faceTwo P 0)

/-- The vertex at `0` is `d1 ∘ d2`. -/
theorem vertexFromHom_const_zero (P : Presentation A B ι σ) :
    vertexFromHom P (SimplexCategory.const ⦋0⦌ ⦋2⦌ 0) =
      (faceOne P).comp (faceTwo P 2) :=
  sorry

/-- The algebra map `P2 → P2` induced by a morphism `⦋2⦌ ⟶ ⦋2⦌`, as a composite of
elementary faces and degeneracies. -/
def term2End (P : Presentation A B ι σ) (φ : ⦋2⦌ ⟶ ⦋2⦌) : term2 P →ₐ[A] term2 P :=
  if φ = 𝟙 _ then
    AlgHom.id A (term2 P)
  else if φ = SimplexCategory.σ 0 ≫ SimplexCategory.δ 2 then
    (degeneracyOne P 0).comp (faceTwo P 2)
  else if φ = SimplexCategory.σ 1 ≫ SimplexCategory.δ 2 then
    (degeneracyOne P 1).comp (faceTwo P 2)
  else if φ = SimplexCategory.σ 0 ≫ SimplexCategory.δ 1 then
    (degeneracyOne P 0).comp (faceTwo P 1)
  else if φ = SimplexCategory.σ 1 ≫ SimplexCategory.δ 1 then
    (degeneracyOne P 1).comp (faceTwo P 1)
  else if φ = SimplexCategory.σ 0 ≫ SimplexCategory.δ 0 then
    (degeneracyOne P 0).comp (faceTwo P 0)
  else if φ = SimplexCategory.σ 1 ≫ SimplexCategory.δ 0 then
    (degeneracyOne P 1).comp (faceTwo P 0)
  else if φ = SimplexCategory.const ⦋2⦌ ⦋2⦌ 0 then
    (rename Vars.u).comp ((faceOne P).comp (faceTwo P 2))
  else if φ = SimplexCategory.const ⦋2⦌ ⦋2⦌ 1 then
    (rename Vars.u).comp ((faceZero P).comp (faceTwo P 2))
  else
    (rename Vars.u).comp ((faceZero P).comp (faceTwo P 0))

/-- The identity morphism of `⦋2⦌` induces the identity on `P2`. -/
theorem term2End_id (P : Presentation A B ι σ) :
    term2End P (𝟙 _) = AlgHom.id A (term2 P) :=
  sorry

/-- The composite `σ j ≫ δ i` induces `s_j ∘ d_i`; in particular `δ 2 ∘ σ 0` is
`s0 ∘ d2`. -/
theorem term2End_σ_comp_δ (P : Presentation A B ι σ) (j : Fin 2) (i : Fin 3) :
    term2End P (SimplexCategory.σ j ≫ SimplexCategory.δ i) =
      (degeneracyOne P j).comp (faceTwo P i) :=
  sorry

/-- Algebra maps of the `1`-truncated object, classified by source and target degree. -/
def hom1 (P : Presentation A B ι σ) :
    ∀ i j : Fin 2, (⦋j.val⦌ ⟶ ⦋i.val⦌) → (alg1 P i ⟶ alg1 P j)
  | ⟨0, _⟩, ⟨0, _⟩, _ => 𝟙 _
  | ⟨0, _⟩, ⟨1, _⟩, _ => CommAlgCat.ofHom (degeneracyZero P)
  | ⟨1, _⟩, ⟨0, _⟩, φ => CommAlgCat.ofHom (faceFromHom P φ)
  | ⟨1, _⟩, ⟨1, _⟩, φ => CommAlgCat.ofHom (term1End P φ)
  | ⟨n + 2, h⟩, _, _ => nomatch h
  | _, ⟨n + 2, h⟩, _ => nomatch h

/-- Algebra maps of the `2`-truncated object, classified by source and target degree. -/
def hom2 (P : Presentation A B ι σ) :
    ∀ i j : Fin 3, (⦋j.val⦌ ⟶ ⦋i.val⦌) → (alg2 P i ⟶ alg2 P j)
  | ⟨0, _⟩, ⟨0, _⟩, _ => 𝟙 _
  | ⟨0, _⟩, ⟨1, _⟩, _ => CommAlgCat.ofHom (degeneracyZero P)
  | ⟨0, _⟩, ⟨2, _⟩, _ => CommAlgCat.ofHom (rename Vars.u)
  | ⟨1, _⟩, ⟨0, _⟩, φ => CommAlgCat.ofHom (faceFromHom P φ)
  | ⟨1, _⟩, ⟨1, _⟩, φ => CommAlgCat.ofHom (term1End P φ)
  | ⟨1, _⟩, ⟨2, _⟩, φ => CommAlgCat.ofHom (degeneracyOneFromHom P φ)
  | ⟨2, _⟩, ⟨0, _⟩, φ => CommAlgCat.ofHom (vertexFromHom P φ)
  | ⟨2, _⟩, ⟨1, _⟩, φ => CommAlgCat.ofHom (faceTwoFromHom P φ)
  | ⟨2, _⟩, ⟨2, _⟩, φ => CommAlgCat.ofHom (term2End P φ)
  | ⟨n + 3, h⟩, _, _ => nomatch h
  | _, ⟨n + 3, h⟩, _ => nomatch h

/-- Slice augmentations of the `1`-truncated algebras. -/
def aug1 (P : Presentation A B ι σ) :
    ∀ i : Fin 2, alg1 P i ⟶ CommAlgCat.of A B
  | ⟨0, _⟩ => CommAlgCat.ofHom (aeval P.val)
  | ⟨1, _⟩ => CommAlgCat.ofHom ((aeval P.val).comp (faceZero P))
  | ⟨n + 2, h⟩ => nomatch h

/-- Slice augmentations of the `2`-truncated algebras. -/
def aug2 (P : Presentation A B ι σ) :
    ∀ i : Fin 3, alg2 P i ⟶ CommAlgCat.of A B
  | ⟨0, _⟩ => CommAlgCat.ofHom (aeval P.val)
  | ⟨1, _⟩ => CommAlgCat.ofHom ((aeval P.val).comp (faceZero P))
  | ⟨2, _⟩ =>
      CommAlgCat.ofHom ((aeval P.val).comp ((faceZero P).comp (faceTwo P 0)))
  | ⟨n + 3, h⟩ => nomatch h

/-- The `1`-truncated objects as arrows to `B`. -/
def over1 (P : Presentation A B ι σ) (i : Fin 2) : Over (CommAlgCat.of A B) :=
  Over.mk (aug1 P i)

/-- The `2`-truncated objects as arrows to `B`. -/
def over2 (P : Presentation A B ι σ) (i : Fin 3) : Over (CommAlgCat.of A B) :=
  Over.mk (aug2 P i)

/-- Slice morphisms of the `1`-truncated object. -/
def overHom1 (P : Presentation A B ι σ) (i j : Fin 2) (φ : ⦋j.val⦌ ⟶ ⦋i.val⦌) :
    over1 P i ⟶ over1 P j :=
  Over.homMk (hom1 P i j φ) sorry

/-- Slice morphisms of the `2`-truncated object. -/
def overHom2 (P : Presentation A B ι σ) (i j : Fin 3) (φ : ⦋j.val⦌ ⟶ ⦋i.val⦌) :
    over2 P i ⟶ over2 P j :=
  Over.homMk (hom2 P i j φ) sorry

/-- The explicit `1`-truncated simplicial object of `A`-algebra maps to `B`. -/
def truncatedOne (P : Presentation A B ι σ) :
    SimplicialObject.Truncated (Over (CommAlgCat.of A B)) 1 where
  obj k := over1 P (deg1 k.unop)
  map {X Y} f := overHom1 P (deg1 X.unop) (deg1 Y.unop) f.unop.hom
  map_id := sorry
  map_comp := sorry

/-- Degree `0` of `truncatedOne` is the presented map `P0 ⟶ B`. -/
theorem truncatedOne_obj_zero (P : Presentation A B ι σ) :
    (truncatedOne P).obj (op (⦋0⦌₁ : SimplexCategory.Truncated 1)) =
      over1 P 0 :=
  sorry

/-- Degree `1` of `truncatedOne` is the presented map `P1 ⟶ B`. -/
theorem truncatedOne_obj_one (P : Presentation A B ι σ) :
    (truncatedOne P).obj (op (⦋1⦌₁ : SimplexCategory.Truncated 1)) =
      over1 P 1 :=
  sorry

/-- The explicit `2`-truncated simplicial object of `A`-algebra maps to `B`. -/
def truncatedTwo (P : Presentation A B ι σ) :
    SimplicialObject.Truncated (Over (CommAlgCat.of A B)) 2 where
  obj k := over2 P (deg2 k.unop)
  map {X Y} f := overHom2 P (deg2 X.unop) (deg2 Y.unop) f.unop.hom
  map_id := sorry
  map_comp := sorry

/-- Degree `0` of `truncatedTwo` is the presented map `P0 ⟶ B`. -/
theorem truncatedTwo_obj_zero (P : Presentation A B ι σ) :
    (truncatedTwo P).obj (op (⦋0⦌₂ : SimplexCategory.Truncated 2)) =
      over2 P 0 :=
  sorry

/-- Degree `1` of `truncatedTwo` is the presented map `P1 ⟶ B`. -/
theorem truncatedTwo_obj_one (P : Presentation A B ι σ) :
    (truncatedTwo P).obj (op (⦋1⦌₂ : SimplexCategory.Truncated 2)) =
      over2 P 1 :=
  sorry

/-- Degree `2` of `truncatedTwo` is the presented map `P2 ⟶ B`. -/
theorem truncatedTwo_obj_two (P : Presentation A B ι σ) :
    (truncatedTwo P).obj (op (⦋2⦌₂ : SimplexCategory.Truncated 2)) =
      over2 P 2 :=
  sorry

/-- The `1`-coskeleton of the explicit `1`-truncated object, in the slice over `B`. -/
noncomputable def coskOne (P : Presentation A B ι σ) :
    SimplicialObject (Over (CommAlgCat.of A B)) :=
  (Truncated.cosk 1).obj (truncatedOne P)

/-- The length-two simplicial object is the `2`-coskeleton of `truncatedTwo`. -/
noncomputable def simplicial (P : Presentation A B ι σ) :
    SimplicialObject (Over (CommAlgCat.of A B)) :=
  (Truncated.cosk 2).obj (truncatedTwo P)

/-- The length-two object is `2`-coskeletal. -/
instance simplicial_isCoskeletal (P : Presentation A B ι σ) :
    (simplicial P).IsCoskeletal 2 :=
  sorry

/-- The forgotten simplicial commutative `A`-algebra of the length-two object. -/
noncomputable def forgetSimplicial (P : Presentation A B ι σ) :
    SimplicialObject (CommAlgCat.{u} A) :=
  simplicial P ⋙ Over.forget (CommAlgCat.of A B)

/-- The forgotten simplicial commutative `A`-algebra of `coskOne`. -/
noncomputable def forgetCoskOne (P : Presentation A B ι σ) :
    SimplicialObject (CommAlgCat.{u} A) :=
  coskOne P ⋙ Over.forget (CommAlgCat.of A B)

/-- The augmentation of `cosk 1` of the explicit `1`-truncated object. -/
noncomputable def coskOneAugmentation (P : Presentation A B ι σ) :
    forgetCoskOne P ⟶
      (const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B) where
  app n := ((coskOne P).obj n).hom
  naturality := sorry

/-- Components of `coskOneAugmentation` are the structure maps of the slice objects. -/
theorem coskOneAugmentation_app (P : Presentation A B ι σ) (n : SimplexCategoryᵒᵖ) :
    (coskOneAugmentation P).app n = ((coskOne P).obj n).hom :=
  sorry

/-- The augmentation `ε : P_• ⟶ B` of the length-two simplicial algebra. -/
noncomputable def augmentation (P : Presentation A B ι σ) :
    forgetSimplicial P ⟶
      (const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B) where
  app n := ((simplicial P).obj n).hom
  naturality := sorry

/-- Components of `augmentation` are the structure maps of the slice objects. -/
theorem augmentation_app (P : Presentation A B ι σ) (n : SimplexCategoryᵒᵖ) :
    (augmentation P).app n = ((simplicial P).obj n).hom :=
  sorry

/-- The joint face map `(d0, d1) : P1 ⟶ P0 ×_B P0` in `CommAlgCat`. -/
noncomputable def toPullback (P : Presentation A B ι σ) :
    CommAlgCat.of A (term1 P) ⟶
      pullback (CommAlgCat.ofHom (aeval P.val)) (CommAlgCat.ofHom (aeval P.val)) :=
  pullback.lift (CommAlgCat.ofHom (faceZero P)) (CommAlgCat.ofHom (faceOne P)) sorry

/-- The two projections of `toPullback` recover `d0` and `d1`. -/
theorem toPullback_fst (P : Presentation A B ι σ) :
    toPullback P ≫ pullback.fst (CommAlgCat.ofHom (aeval P.val))
        (CommAlgCat.ofHom (aeval P.val)) =
      CommAlgCat.ofHom (faceZero P) :=
  sorry

/-- The second projection of `toPullback` recovers `d1`. -/
theorem toPullback_snd (P : Presentation A B ι σ) :
    toPullback P ≫ pullback.snd (CommAlgCat.ofHom (aeval P.val))
        (CommAlgCat.ofHom (aeval P.val)) =
      CommAlgCat.ofHom (faceOne P) :=
  sorry

/-- The compatible face family of `d0, d1, d2 : P2 ⟶ P1`. -/
def faceTwoFamily (P : Presentation A B ι σ) :
    matching.FaceFamily (truncatedOne P) (over2 P 2) where
  app i := Over.homMk (CommAlgCat.ofHom (faceTwo P i)) sorry
  compatible := sorry

/-- The underlying algebra map of `faceTwoFamily` is the face `d_i`. -/
theorem faceTwoFamily_app_left (P : Presentation A B ι σ) (i : Fin 3) :
    ((faceTwoFamily P).app i).left = CommAlgCat.ofHom (faceTwo P i) :=
  sorry

/-- The polynomial surjection `P2 ⟶ cosk1(P)_2` onto the matching object. -/
noncomputable def toMatching (P : Presentation A B ι σ) :
    over2 P 2 ⟶ matching.object (truncatedOne P) :=
  (matching.object.representableBy (truncatedOne P)).homEquiv.symm (faceTwoFamily P)

/-- `toMatching` represents the face family `(d0, d1, d2)`. -/
theorem toMatching_homEquiv (P : Presentation A B ι σ) :
    (matching.object.representableBy (truncatedOne P)).homEquiv (toMatching P) =
      faceTwoFamily P :=
  sorry

/-- Each term `P0`, `P1`, `P2` is a polynomial `A`-algebra. -/
instance instIsPolynomial_term0 (P : Presentation A B ι σ) :
    Algebra.IsPolynomial A (term0 P) :=
  inferInstance

/-- `P1` is a polynomial `A`-algebra. -/
instance instIsPolynomial_term1 (P : Presentation A B ι σ) :
    Algebra.IsPolynomial A (term1 P) :=
  MvPolynomial.instIsPolynomial

/-- `P2` is a polynomial `A`-algebra. -/
instance instIsPolynomial_term2 (P : Presentation A B ι σ) :
    Algebra.IsPolynomial A (term2 P) :=
  MvPolynomial.instIsPolynomial

end

end Algebra.Presentation.LengthTwo
