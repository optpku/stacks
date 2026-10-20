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
public import ReasLib.RingTheory.Extension.Presentation.LengthTwo.Terms
public import ReasLib.AlgebraicTopology.SimplicialObject.PolynomialAugmentation

/-!
# Length-two simplicial polynomial diagrams

The construction packages the explicit `P0`, `P1`, `P2` data of a presentation as truncated
simplicial objects in the slice `Over (CommAlgCat.of A B)`, together with the
`2`-coskeleton, matching map, and forgotten augmentation.
-/

public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open CategoryTheory.SimplicialObject.Truncated
open Opposite
open Algebra
open Algebra.Presentation.LengthTwo
open MvPolynomial
open Algebra.PolynomialSite
open SSet.modelCategoryQuillen
open scoped Simplicial SimplexCategory.Truncated

universe u

namespace Algebra.Presentation.LengthTwo

variable {A B ι σ : Type u} [CommRing A] [CommRing B] [Algebra A B]

noncomputable section

/-- The `1`-truncated coefficient algebras `P0` and `P1`. -/
@[expose]
def alg1 (P : Presentation A B ι σ) : Fin 2 → CommAlgCat.{u} A
  | ⟨0, _⟩ => CommAlgCat.of A (term0 P)
  | ⟨1, _⟩ => CommAlgCat.of A (term1 P)
  | ⟨n + 2, h⟩ => nomatch h

/-- The `2`-truncated coefficient algebras `P0`, `P1`, and `P2`. -/
@[expose]
def alg2 (P : Presentation A B ι σ) : Fin 3 → CommAlgCat.{u} A
  | ⟨0, _⟩ => CommAlgCat.of A (term0 P)
  | ⟨1, _⟩ => CommAlgCat.of A (term1 P)
  | ⟨2, _⟩ => CommAlgCat.of A (term2 P)
  | ⟨n + 3, h⟩ => nomatch h

/-- The face `P1 → P0` selected by a coface `δ i : ⦋0⦌ ⟶ ⦋1⦌`. -/
private def faceFromHom (P : Presentation A B ι σ) (φ : ⦋0⦌ ⟶ ⦋1⦌) : term1 P →ₐ[A] P.Ring :=
  if φ = SimplexCategory.δ 0 then faceZero P else faceOne P

/-- Identity, `s0 ∘ d1`, or `s0 ∘ d0` according to a morphism `⦋1⦌ ⟶ ⦋1⦌`. -/
private def term1End (P : Presentation A B ι σ) (φ : ⦋1⦌ ⟶ ⦋1⦌) : term1 P →ₐ[A] term1 P :=
  if φ = 𝟙 _ then AlgHom.id A (term1 P)
  else if φ = SimplexCategory.const ⦋1⦌ ⦋1⦌ 0 then (degeneracyZero P).comp (faceOne P)
  else (degeneracyZero P).comp (faceZero P)

/-- The algebra map `P2 → P1` induced by a morphism `⦋1⦌ ⟶ ⦋2⦌`, as a composite of
elementary faces and degeneracies. -/
private def faceTwoFromHom (P : Presentation A B ι σ) (φ : ⦋1⦌ ⟶ ⦋2⦌) : term2 P →ₐ[A] term1 P :=
  if φ = SimplexCategory.δ 0 then faceTwo P 0
  else if φ = SimplexCategory.δ 1 then faceTwo P 1
  else if φ = SimplexCategory.δ 2 then faceTwo P 2
  else if φ = SimplexCategory.const ⦋1⦌ ⦋2⦌ 0 then
    (degeneracyZero P).comp ((faceOne P).comp (faceTwo P 2))
  else if φ = SimplexCategory.const ⦋1⦌ ⦋2⦌ 1 then
    (degeneracyZero P).comp ((faceZero P).comp (faceTwo P 2))
  else
    (degeneracyZero P).comp ((faceZero P).comp (faceTwo P 0))

/-- The algebra map `P1 → P2` induced by a morphism `⦋2⦌ ⟶ ⦋1⦌`, as a composite of
elementary faces and degeneracies. -/
private def degeneracyOneFromHom (P : Presentation A B ι σ) (φ : ⦋2⦌ ⟶ ⦋1⦌) :
    term1 P →ₐ[A] term2 P :=
  if φ = SimplexCategory.σ 0 then degeneracyOne P 0
  else if φ = SimplexCategory.σ 1 then degeneracyOne P 1
  else if φ = SimplexCategory.const ⦋2⦌ ⦋1⦌ 0 then (rename Vars.u).comp (faceOne P)
  else (rename Vars.u).comp (faceZero P)

/-- Vertex maps `P2 → P0` selected by a morphism `⦋0⦌ ⟶ ⦋2⦌`. -/
private def vertexFromHom (P : Presentation A B ι σ) (φ : ⦋0⦌ ⟶ ⦋2⦌) : term2 P →ₐ[A] P.Ring :=
  if φ = SimplexCategory.const ⦋0⦌ ⦋2⦌ 0 then (faceOne P).comp (faceTwo P 2)
  else if φ = SimplexCategory.const ⦋0⦌ ⦋2⦌ 1 then (faceZero P).comp (faceTwo P 2)
  else (faceZero P).comp (faceTwo P 0)

/-- The algebra map `P2 → P2` induced by a morphism `⦋2⦌ ⟶ ⦋2⦌`, as a composite of
elementary faces and degeneracies. -/
private def term2End (P : Presentation A B ι σ) (φ : ⦋2⦌ ⟶ ⦋2⦌) : term2 P →ₐ[A] term2 P :=
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
@[expose]
def aug1 (P : Presentation A B ι σ) :
    ∀ i : Fin 2, alg1 P i ⟶ CommAlgCat.of A B
  | ⟨0, _⟩ => CommAlgCat.ofHom (aeval P.val)
  | ⟨1, _⟩ => CommAlgCat.ofHom ((aeval P.val).comp (faceZero P))
  | ⟨n + 2, h⟩ => nomatch h

/-- Slice augmentations of the `2`-truncated algebras. -/
@[expose]
def aug2 (P : Presentation A B ι σ) :
    ∀ i : Fin 3, alg2 P i ⟶ CommAlgCat.of A B
  | ⟨0, _⟩ => CommAlgCat.ofHom (aeval P.val)
  | ⟨1, _⟩ => CommAlgCat.ofHom ((aeval P.val).comp (faceZero P))
  | ⟨2, _⟩ =>
      CommAlgCat.ofHom ((aeval P.val).comp ((faceZero P).comp (faceTwo P 0)))
  | ⟨n + 3, h⟩ => nomatch h

/-- The `1`-truncated objects as arrows to `B`. -/
@[expose]
def over1 (P : Presentation A B ι σ) (i : Fin 2) : Over (CommAlgCat.of A B) :=
  Over.mk (aug1 P i)

/-- The `2`-truncated objects as arrows to `B`. -/
@[expose]
def over2 (P : Presentation A B ι σ) (i : Fin 3) : Over (CommAlgCat.of A B) :=
  Over.mk (aug2 P i)

/-- Every structure map of the one-truncated diagram commutes with augmentation. -/
theorem overHom1_comm (P : Presentation A B ι σ) (i j : Fin 2)
    (φ : ⦋j.val⦌ ⟶ ⦋i.val⦌) :
    hom1 P i j φ ≫ aug1 P j = aug1 P i :=
  sorry

/-- Every structure map of the two-truncated diagram commutes with augmentation. -/
theorem overHom2_comm (P : Presentation A B ι σ) (i j : Fin 3)
    (φ : ⦋j.val⦌ ⟶ ⦋i.val⦌) :
    hom2 P i j φ ≫ aug2 P j = aug2 P i :=
  sorry

/-- Identity simplex maps induce identity algebra maps in degrees zero and one. -/
theorem hom1_id (P : Presentation A B ι σ) (i : Fin 2) :
    hom1 P i i (𝟙 _) = 𝟙 (alg1 P i) :=
  sorry

/-- The one-truncated algebra-map assignment reverses composition of simplex maps. -/
theorem hom1_comp (P : Presentation A B ι σ) (i j k : Fin 2)
    (φ : ⦋j.val⦌ ⟶ ⦋i.val⦌) (ψ : ⦋k.val⦌ ⟶ ⦋j.val⦌) :
    hom1 P i k (ψ ≫ φ) = hom1 P i j φ ≫ hom1 P j k ψ :=
  sorry

/-- Identity simplex maps induce identity algebra maps through degree two. -/
theorem hom2_id (P : Presentation A B ι σ) (i : Fin 3) :
    hom2 P i i (𝟙 _) = 𝟙 (alg2 P i) :=
  sorry

/-- The two-truncated algebra-map assignment reverses composition of simplex maps. -/
theorem hom2_comp (P : Presentation A B ι σ) (i j k : Fin 3)
    (φ : ⦋j.val⦌ ⟶ ⦋i.val⦌) (ψ : ⦋k.val⦌ ⟶ ⦋j.val⦌) :
    hom2 P i k (ψ ≫ φ) = hom2 P i j φ ≫ hom2 P j k ψ :=
  sorry

/-- Slice morphisms of the `1`-truncated object. -/
@[expose]
def overHom1 (P : Presentation A B ι σ) (i j : Fin 2) (φ : ⦋j.val⦌ ⟶ ⦋i.val⦌) :
    over1 P i ⟶ over1 P j :=
  Over.homMk (hom1 P i j φ) (overHom1_comm P i j φ)

/-- Slice morphisms of the `2`-truncated object. -/
@[expose]
def overHom2 (P : Presentation A B ι σ) (i j : Fin 3) (φ : ⦋j.val⦌ ⟶ ⦋i.val⦌) :
    over2 P i ⟶ over2 P j :=
  Over.homMk (hom2 P i j φ) (overHom2_comm P i j φ)

/-- The explicit `1`-truncated simplicial object of `A`-algebra maps to `B`. -/
@[expose]
def truncatedOne (P : Presentation A B ι σ) :
    SimplicialObject.Truncated (Over (CommAlgCat.of A B)) 1 where
  obj k := over1 P (SimplexCategory.Truncated.objEquiv.inverse k.unop)
  map {X Y} f := overHom1 P (SimplexCategory.Truncated.objEquiv.inverse X.unop)
    (SimplexCategory.Truncated.objEquiv.inverse Y.unop) f.unop.hom
  map_id X := by
    apply Over.OverMorphism.ext
    exact hom1_id P _
  map_comp {X Y Z} f g := by
    apply Over.OverMorphism.ext
    exact hom1_comp P (SimplexCategory.Truncated.objEquiv.inverse X.unop)
      (SimplexCategory.Truncated.objEquiv.inverse Y.unop)
      (SimplexCategory.Truncated.objEquiv.inverse Z.unop) f.unop.hom g.unop.hom

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
@[expose]
def truncatedTwo (P : Presentation A B ι σ) :
    SimplicialObject.Truncated (Over (CommAlgCat.of A B)) 2 where
  obj k := over2 P (SimplexCategory.Truncated.objEquiv.inverse k.unop)
  map {X Y} f := overHom2 P (SimplexCategory.Truncated.objEquiv.inverse X.unop)
    (SimplexCategory.Truncated.objEquiv.inverse Y.unop) f.unop.hom
  map_id X := by
    apply Over.OverMorphism.ext
    exact hom2_id P _
  map_comp {X Y Z} f g := by
    apply Over.OverMorphism.ext
    exact hom2_comp P (SimplexCategory.Truncated.objEquiv.inverse X.unop)
      (SimplexCategory.Truncated.objEquiv.inverse Y.unop)
      (SimplexCategory.Truncated.objEquiv.inverse Z.unop) f.unop.hom g.unop.hom

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
@[expose]
noncomputable def coskOne (P : Presentation A B ι σ) :
    SimplicialObject (Over (CommAlgCat.of A B)) :=
  (Truncated.cosk 1).obj (truncatedOne P)

/-- The auxiliary simplicial algebra is the two-coskeleton of the explicit polynomial diagram. -/
@[expose]
noncomputable def simplicial (P : Presentation A B ι σ) :
    SimplicialObject (Over (CommAlgCat.of A B)) :=
  (Truncated.cosk 2).obj (truncatedTwo P)

/-- The auxiliary two-coskeleton is two-coskeletal. -/
instance simplicial_isCoskeletal (P : Presentation A B ι σ) :
    (simplicial P).IsCoskeletal 2 :=
  sorry

/-- The underlying simplicial commutative algebra of the auxiliary two-coskeleton. -/
@[expose]
noncomputable def forgetSimplicial (P : Presentation A B ι σ) :
    SimplicialObject (CommAlgCat.{u} A) :=
  simplicial P ⋙ Over.forget (CommAlgCat.of A B)

/-- The forgotten simplicial commutative `A`-algebra of `coskOne`. -/
@[expose]
noncomputable def forgetCoskOne (P : Presentation A B ι σ) :
    SimplicialObject (CommAlgCat.{u} A) :=
  coskOne P ⋙ Over.forget (CommAlgCat.of A B)

/-- The augmentation of `cosk 1` of the explicit `1`-truncated object. -/
@[expose]
noncomputable def coskOneAugmentation (P : Presentation A B ι σ) :
    forgetCoskOne P ⟶
      (const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B) where
  app n := ((coskOne P).obj n).hom
  naturality {X Y} f := by
    change ((coskOne P).map f).left ≫ ((coskOne P).obj Y).hom =
      ((coskOne P).obj X).hom ≫ 𝟙 _
    rw [Category.comp_id]
    exact Over.w ((coskOne P).map f)

/-- Components of `coskOneAugmentation` are the structure maps of the slice objects. -/
theorem coskOneAugmentation_app (P : Presentation A B ι σ) (n : SimplexCategoryᵒᵖ) :
    (coskOneAugmentation P).app n = ((coskOne P).obj n).hom :=
  sorry

/-- The augmentation of the auxiliary two-coskeleton to the presented algebra. -/
@[expose]
noncomputable def augmentation (P : Presentation A B ι σ) :
    forgetSimplicial P ⟶
      (const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B) where
  app n := ((simplicial P).obj n).hom
  naturality {X Y} f := by
    change ((simplicial P).map f).left ≫ ((simplicial P).obj Y).hom =
      ((simplicial P).obj X).hom ≫ 𝟙 _
    rw [Category.comp_id]
    exact Over.w ((simplicial P).map f)

/-- Components of `augmentation` are the structure maps of the slice objects. -/
theorem augmentation_app (P : Presentation A B ι σ) (n : SimplexCategoryᵒᵖ) :
    (augmentation P).app n = ((simplicial P).obj n).hom :=
  sorry

/-- The joint face map `(d0, d1) : P1 ⟶ P0 ×_B P0` in `CommAlgCat`. -/
@[expose]
noncomputable def toPullback (P : Presentation A B ι σ) :
    CommAlgCat.of A (term1 P) ⟶
      pullback (CommAlgCat.ofHom (aeval P.val)) (CommAlgCat.ofHom (aeval P.val)) :=
  pullback.lift (CommAlgCat.ofHom (faceZero P)) (CommAlgCat.ofHom (faceOne P)) (by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro p
    exact toProd_comp_aeval P p)

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

/-- Each degree-two face commutes with the augmentation to the presented algebra. -/
theorem faceTwo_augmentation (P : Presentation A B ι σ) (i : Fin 3) :
    CommAlgCat.ofHom (faceTwo P i) ≫ aug1 P 1 = aug2 P 2 :=
  sorry

/-- The degree-two face maps regarded as morphisms over the presented algebra. -/
@[expose]
def faceTwoOver (P : Presentation A B ι σ) (i : Fin 3) :
    over2 P 2 ⟶ over1 P 1 :=
  Over.homMk (CommAlgCat.ofHom (faceTwo P i)) (faceTwo_augmentation P i)

/-- The three degree-two faces satisfy the matching-family compatibility equations. -/
theorem faceTwoFamily_compatible (P : Presentation A B ι σ) :
    matching.FaceFamily.Compatible (truncatedOne P) (faceTwoOver P) :=
  sorry

/-- The compatible face family of `d0, d1, d2 : P2 ⟶ P1`. -/
@[expose]
def faceTwoFamily (P : Presentation A B ι σ) :
    matching.FaceFamily (truncatedOne P) (over2 P 2) where
  app := faceTwoOver P
  compatible := faceTwoFamily_compatible P

/-- The underlying algebra map of `faceTwoFamily` is the face `d_i`. -/
theorem faceTwoFamily_app_left (P : Presentation A B ι σ) (i : Fin 3) :
    ((faceTwoFamily P).app i).left = CommAlgCat.ofHom (faceTwo P i) :=
  sorry

/-- The map from the degree-two polynomial algebra to the canonical matching object. -/
@[expose]
noncomputable def toMatching (P : Presentation A B ι σ) :
    over2 P 2 ⟶ matching.object (truncatedOne P) :=
  (matching.object.representableBy (truncatedOne P)).homEquiv.symm (faceTwoFamily P)

/-- `toMatching` represents the face family `(d0, d1, d2)`. -/
theorem toMatching_homEquiv (P : Presentation A B ι σ) :
    (matching.object.representableBy (truncatedOne P)).homEquiv (toMatching P) =
      faceTwoFamily P :=
  sorry

/-- The difference of the degree-one faces is exact at the degree-zero polynomial algebra, and evaluation onto the presented algebra is surjective. -/
theorem exact_faceSub (P : Presentation A B ι σ) :
    Function.Exact (fun p : term1 P ↦ faceZero P p - faceOne P p)
        (fun p : P.Ring ↦ aeval P.val p) ∧
      Function.Surjective (fun p : P.Ring ↦ aeval P.val p) :=
  sorry

/-- Every pair of degree-zero polynomials with equal evaluation lifts along the joint face map. -/
theorem toPullback_surjective (P : Presentation A B ι σ) {p0 p1 : P.Ring}
    (h : aeval P.val p0 = aeval P.val p1) :
    ∃ q : term1 P, faceZero P q = p0 ∧ faceOne P q = p1 :=
  sorry

/-- The augmentation of the one-coskeleton is a trivial Kan fibration on underlying simplicial sets. -/
theorem coskOne_trivialKan (P : Presentation A B ι σ) :
    I.rlp (underlyingSSetMap (coskOneAugmentation P)) :=
  sorry

/-- Every compatible triple of degree-one polynomials lifts along the three degree-two faces. -/
theorem toMatching_surjective (P : Presentation A B ι σ)
    {g0 g1 g2 : term1 P} (h : Triple.Compatible P g0 g1 g2) :
    ∃ q : term2 P,
      faceTwo P 0 q = g0 ∧ faceTwo P 1 q = g1 ∧ faceTwo P 2 q = g2 :=
  sorry

end

end Algebra.Presentation.LengthTwo
