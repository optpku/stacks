module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Single.Object
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.StructureMaps

/-!
# Top-degree compatibility data for truncated simplicial objects

This leaf owns the face- and degeneracy-vanishing conditions, their bundled top-degree maps, and
the functorial transport API.  It is independent of the functorial concentrated-object layer.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open SimplexCategory
open scoped SimplexCategory.Truncated Simplicial

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

namespace concentrated

/-- The top face-vanishing condition on a morphism into a truncated simplicial object. -/
@[stacks 0190 "concentrated face condition"]
def FaceCondition {k : ℕ} (V : SimplicialObject.Truncated A k) {B : A}
    (f : B ⟶ V.obj (op (top k))) : Prop :=
  match k with
  | 0 => True
  | n + 1 =>
      ∀ i : Fin (n + 2), f ≫ V.δ i = 0

/-- The top degeneracy-vanishing condition on a morphism out of a truncated simplicial object. -/
@[stacks 0190 "concentrated degeneracy condition"]
def DegeneracyCondition {k : ℕ} (V : SimplicialObject.Truncated A k) {B : A}
    (f : V.obj (op (top k)) ⟶ B) : Prop :=
  match k with
  | 0 => True
  | n + 1 =>
      ∀ i : Fin (n + 1), V.σ i ≫ f = 0

/-- A face-compatible map from an object to the top degree of a truncated simplicial object. -/
@[stacks 0190 "face-compatible top-degree map"]
abbrev FaceMap {k : ℕ} (B : A) (V : SimplicialObject.Truncated A k) :=
  { f : B ⟶ V.obj (op (top k)) // FaceCondition V f }

/-- A degeneracy-compatible map from the top degree of a truncated simplicial object to an
object. -/
@[stacks 0190 "degeneracy-compatible top-degree map"]
abbrev DegeneracyMap {k : ℕ} (V : SimplicialObject.Truncated A k) (B : A) :=
  { f : V.obj (op (top k)) ⟶ B // DegeneracyCondition V f }

/-- Face compatibility is preserved by precomposition in the source object. -/
@[stacks 0190 "face compatibility under source precomposition"]
theorem FaceCondition.precomp {k : ℕ} {V : SimplicialObject.Truncated A k}
    {B B' : A} {f : B ⟶ V.obj (op (top k))} (hf : FaceCondition V f)
    (g : B' ⟶ B) : FaceCondition V (g ≫ f) := sorry

/-- Face compatibility is preserved by postcomposition with a morphism of truncated simplicial
objects. -/
@[stacks 0190 "face compatibility under target postcomposition"]
theorem FaceCondition.postcomp {k : ℕ} {V W : SimplicialObject.Truncated A k}
    {B : A} {f : B ⟶ V.obj (op (top k))} (hf : FaceCondition V f)
    (g : V ⟶ W) : FaceCondition W (f ≫ g.app (op (top k))) := sorry

/-- Degeneracy compatibility is preserved by postcomposition in the target object. -/
@[stacks 0190 "degeneracy compatibility under target postcomposition"]
theorem DegeneracyCondition.postcomp {k : ℕ} {V : SimplicialObject.Truncated A k}
    {B B' : A} {f : V.obj (op (top k)) ⟶ B} (hf : DegeneracyCondition V f)
    (g : B ⟶ B') : DegeneracyCondition V (f ≫ g) := sorry

/-- Degeneracy compatibility is preserved by precomposition with a morphism of truncated
simplicial objects. -/
@[stacks 0190 "degeneracy compatibility under source precomposition"]
theorem DegeneracyCondition.precomp {k : ℕ} {V W : SimplicialObject.Truncated A k}
    {B : A} {f : W.obj (op (top k)) ⟶ B} (hf : DegeneracyCondition W f)
    (g : V ⟶ W) : DegeneracyCondition V (g.app (op (top k)) ≫ f) := sorry

namespace FaceMap

/-- Precompose face-compatible top-degree data in its source object. -/
@[stacks 0190 "precomposition of face-compatible top-degree maps"]
def precomp {k : ℕ} {B B' : A} {V : SimplicialObject.Truncated A k}
    (f : FaceMap B V) (g : B' ⟶ B) : FaceMap B' V :=
  ⟨g ≫ f.1, FaceCondition.precomp f.2 g⟩

/-- The underlying map of `FaceMap.precomp` is ordinary composition. -/
@[simp, stacks 0190 "underlying precomposition of a face-compatible map"]
theorem precomp.val {k : ℕ} {B B' : A} {V : SimplicialObject.Truncated A k}
    (f : FaceMap B V) (g : B' ⟶ B) : (f.precomp g).1 = g ≫ f.1 := sorry

/-- Postcompose face-compatible top-degree data with a morphism of truncated simplicial
objects. -/
@[stacks 0190 "postcomposition of face-compatible top-degree maps"]
def postcomp {k : ℕ} {B : A} {V W : SimplicialObject.Truncated A k}
    (f : FaceMap B V) (g : V ⟶ W) : FaceMap B W :=
  ⟨f.1 ≫ g.app (op (top k)), FaceCondition.postcomp f.2 g⟩

/-- The underlying map of `FaceMap.postcomp` is ordinary composition at top degree. -/
@[simp, stacks 0190 "underlying postcomposition of a face-compatible map"]
theorem postcomp.val {k : ℕ} {B : A} {V W : SimplicialObject.Truncated A k}
    (f : FaceMap B V) (g : V ⟶ W) :
    (f.postcomp g).1 = f.1 ≫ g.app (op (top k)) := sorry

/-- Precomposition by an identity leaves face-compatible data unchanged. -/
@[simp, stacks 0190 "identity precomposition of face-compatible maps"]
theorem precomp.id {k : ℕ} {B : A} {V : SimplicialObject.Truncated A k}
    (f : FaceMap B V) : f.precomp (𝟙 B) = f := sorry

/-- Successive source precompositions of face-compatible data combine by composition. -/
@[simp, stacks 0190 "composition of face-compatible source precompositions"]
theorem precomp.comp {k : ℕ} {B B' B'' : A} {V : SimplicialObject.Truncated A k}
    (f : FaceMap B V) (g : B' ⟶ B) (h : B'' ⟶ B') :
    (f.precomp g).precomp h = f.precomp (h ≫ g) := sorry

/-- Postcomposition by an identity leaves face-compatible data unchanged. -/
@[simp, stacks 0190 "identity postcomposition of face-compatible maps"]
theorem postcomp.id {k : ℕ} {B : A} {V : SimplicialObject.Truncated A k}
    (f : FaceMap B V) : f.postcomp (𝟙 V) = f := sorry

/-- Successive target postcompositions of face-compatible data combine by composition. -/
@[simp, stacks 0190 "composition of face-compatible target postcompositions"]
theorem postcomp.comp {k : ℕ} {B : A}
    {U V W : SimplicialObject.Truncated A k} (f : FaceMap B U)
    (g : U ⟶ V) (h : V ⟶ W) :
    (f.postcomp g).postcomp h = f.postcomp (g ≫ h) := sorry

/-- Source precomposition and target postcomposition commute on face-compatible data. -/
@[stacks 0190 "interchange for face-compatible map transport"]
theorem precomp_postcomp {k : ℕ} {B B' : A}
    {V W : SimplicialObject.Truncated A k} (f : FaceMap B V)
    (g : B' ⟶ B) (h : V ⟶ W) :
    (f.precomp g).postcomp h = (f.postcomp h).precomp g := sorry

end FaceMap

namespace DegeneracyMap

/-- Postcompose degeneracy-compatible top-degree data in its target object. -/
@[stacks 0190 "postcomposition of degeneracy-compatible top-degree maps"]
def postcomp {k : ℕ} {V : SimplicialObject.Truncated A k} {B B' : A}
    (f : DegeneracyMap V B) (g : B ⟶ B') : DegeneracyMap V B' :=
  ⟨f.1 ≫ g, DegeneracyCondition.postcomp f.2 g⟩

/-- The underlying map of `DegeneracyMap.postcomp` is ordinary composition. -/
@[simp, stacks 0190 "underlying postcomposition of a degeneracy-compatible map"]
theorem postcomp.val {k : ℕ} {V : SimplicialObject.Truncated A k} {B B' : A}
    (f : DegeneracyMap V B) (g : B ⟶ B') : (f.postcomp g).1 = f.1 ≫ g := sorry

/-- Precompose degeneracy-compatible top-degree data with a morphism of truncated simplicial
objects. -/
@[stacks 0190 "precomposition of degeneracy-compatible top-degree maps"]
def precomp {k : ℕ} {V W : SimplicialObject.Truncated A k} {B : A}
    (f : DegeneracyMap W B) (g : V ⟶ W) : DegeneracyMap V B :=
  ⟨g.app (op (top k)) ≫ f.1, DegeneracyCondition.precomp f.2 g⟩

/-- The underlying map of `DegeneracyMap.precomp` is ordinary composition at top degree. -/
@[simp, stacks 0190 "underlying precomposition of a degeneracy-compatible map"]
theorem precomp.val {k : ℕ} {V W : SimplicialObject.Truncated A k} {B : A}
    (f : DegeneracyMap W B) (g : V ⟶ W) :
    (f.precomp g).1 = g.app (op (top k)) ≫ f.1 := sorry

/-- Postcomposition by an identity leaves degeneracy-compatible data unchanged. -/
@[simp, stacks 0190 "identity postcomposition of degeneracy-compatible maps"]
theorem postcomp.id {k : ℕ} {V : SimplicialObject.Truncated A k} {B : A}
    (f : DegeneracyMap V B) : f.postcomp (𝟙 B) = f := sorry

/-- Successive target postcompositions of degeneracy-compatible data combine by composition. -/
@[simp, stacks 0190 "composition of degeneracy-compatible target postcompositions"]
theorem postcomp.comp {k : ℕ} {V : SimplicialObject.Truncated A k} {B B' B'' : A}
    (f : DegeneracyMap V B) (g : B ⟶ B') (h : B' ⟶ B'') :
    (f.postcomp g).postcomp h = f.postcomp (g ≫ h) := sorry

/-- Precomposition by an identity leaves degeneracy-compatible data unchanged. -/
@[simp, stacks 0190 "identity precomposition of degeneracy-compatible maps"]
theorem precomp.id {k : ℕ} {V : SimplicialObject.Truncated A k} {B : A}
    (f : DegeneracyMap V B) : f.precomp (𝟙 V) = f := sorry

/-- Successive source precompositions of degeneracy-compatible data combine by composition. -/
@[simp, stacks 0190 "composition of degeneracy-compatible source precompositions"]
theorem precomp.comp {k : ℕ} {U V W : SimplicialObject.Truncated A k} {B : A}
    (f : DegeneracyMap W B) (g : V ⟶ W) (h : U ⟶ V) :
    (f.precomp g).precomp h = f.precomp (h ≫ g) := sorry

/-- Source precomposition and target postcomposition commute on degeneracy-compatible data. -/
@[stacks 0190 "interchange for degeneracy-compatible map transport"]
theorem precomp_postcomp {k : ℕ} {V W : SimplicialObject.Truncated A k}
    {B B' : A} (f : DegeneracyMap W B) (g : V ⟶ W) (h : B ⟶ B') :
    (f.precomp g).postcomp h = (f.postcomp h).precomp g := sorry

end DegeneracyMap

/-- In positive top degree, `FaceCondition` is the family of face-vanishing equations. -/
@[simp, stacks 0190 "positive-degree concentrated face condition"]
theorem FaceCondition.succ_iff (n : ℕ)
    (V : SimplicialObject.Truncated A (n + 1)) {B : A}
    (f : B ⟶ V.obj (op (top (n + 1)))) :
    FaceCondition V f ↔
      ∀ i : Fin (n + 2), f ≫ V.δ i = 0 := sorry

/-- In positive top degree, `DegeneracyCondition` is the family of degeneracy-vanishing
equations. -/
@[simp, stacks 0190 "positive-degree concentrated degeneracy condition"]
theorem DegeneracyCondition.succ_iff (n : ℕ)
    (V : SimplicialObject.Truncated A (n + 1)) {B : A}
    (f : V.obj (op (top (n + 1))) ⟶ B) :
    DegeneracyCondition V f ↔
      ∀ i : Fin (n + 1), V.σ i ≫ f = 0 := sorry

end concentrated

end CategoryTheory.SimplicialObject.Truncated
