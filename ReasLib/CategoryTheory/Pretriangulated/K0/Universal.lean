/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.K0.Additivity

@[expose] public section

/-!
# The Universal Property of Triangulated Grothendieck Groups

An object-valued additive invariant descends to `TriangulatedK0` as soon as it
is additive on distinguished triangles.  The resulting maps are determined by
their values on object classes and are invariant under natural isomorphisms of
exact functors.
-/

open CategoryTheory.Pretriangulated
open CategoryTheory.Limits

universe v u v₁ u₁ v₂ u₂

namespace CategoryTheory.TriangulatedK0

section Lift

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
variable {M : Type*} [AddCommGroup M]

/-- A function that is additive on distinguished triangles kills the defining
relations of the triangulated Grothendieck group. -/
theorem relations_le_ker_of_distinguished (f : C → M)
    (hf : ∀ (T : Triangle C), T ∈ distTriang C → f T.obj₂ = f T.obj₁ + f T.obj₃) :
    relations C ≤ (FreeAbelianGroup.lift f).ker := sorry

/-- Descend a function on objects to the triangulated Grothendieck group from
its additivity on distinguished triangles. -/
def liftOfDistinguished (f : C → M)
    (hf : ∀ (T : Triangle C), T ∈ distTriang C → f T.obj₂ = f T.obj₁ + f T.obj₃) :
    TriangulatedK0 C →+ M :=
  lift f (relations_le_ker_of_distinguished f hf)

/-- The lift of a distinguished-triangle-additive invariant agrees with the
original invariant on object classes. -/
@[simp]
theorem liftOfDistinguished_of (f : C → M)
    (hf : ∀ (T : Triangle C), T ∈ distTriang C → f T.obj₂ = f T.obj₁ + f T.obj₃)
    (X : C) :
    liftOfDistinguished f hf (of X) = f X := sorry

/-- Additive homomorphisms from a triangulated Grothendieck group are equal
when they agree on every object class. -/
@[ext]
theorem hom_ext (f g : TriangulatedK0 C →+ M)
    (h : ∀ X : C, f (of X) = g (of X)) : f = g := sorry

end Lift

section Functoriality

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Preadditive C₁] [HasZeroObject C₁]
  [HasShift C₁ ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor C₁ n)] [Pretriangulated C₁]
variable {C₂ : Type u₂} [Category.{v₂} C₂] [Preadditive C₂] [HasZeroObject C₂]
  [HasShift C₂ ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor C₂ n)] [Pretriangulated C₂]

/-- Naturally isomorphic exact functors induce the same homomorphism on
triangulated Grothendieck groups. -/
theorem map_eq_of_iso {F G : C₁ ⥤ C₂} [F.CommShift ℤ] [F.IsTriangulated]
    [G.CommShift ℤ] [G.IsTriangulated] (e : F ≅ G) :
    map F = map G := sorry

end Functoriality

end CategoryTheory.TriangulatedK0
