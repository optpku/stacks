module

public import ReasLib.AlgebraicTopology.DoldKan.Equivalence
public import Mathlib.AlgebraicTopology.SimplicialObject.Op
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The lower-face normalized Moore complex

Reversing the simplex indexing turns Mathlib's normalized Moore complex into the convention whose
degree-`n` object is the intersection of the kernels of `d₀, ..., dₙ₋₁`. This file owns that chain
complex as a functor and equivalence, together with its subobject and differential coordinates.

@stack 017V
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicTopology
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.Abelian.DoldKan.N

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The lower-face normalized Moore complex, obtained by reversing simplex indices before
applying Mathlib's normalized Moore functor. -/
@[stacks 017V "lower-face normalized Moore functor"]
noncomputable abbrev lowerFace :
    SimplicialObject A ⥤ ChainComplex A ℕ :=
  _root_.SimplicialObject.opFunctor ⋙ N

/-- The Dold--Kan equivalence in the lower-face normalization convention. -/
@[stacks 017W "lower-face Dold--Kan equivalence"]
noncomputable def lowerFace.equivalence :
    SimplicialObject A ≌ ChainComplex A ℕ :=
  _root_.SimplicialObject.opEquivalence.trans Abelian.DoldKan.equivalence

/-- The lower-face normalized Moore functor is an equivalence. -/
@[stacks 017W "lower-face normalization is an equivalence"]
instance lowerFace.isEquivalence :
    (lowerFace : SimplicialObject A ⥤ ChainComplex A ℕ).IsEquivalence := sorry

/-- The lower-face normalized Moore functor bundled as an exact functor. -/
@[stacks 017W "exact lower-face normalized Moore functor"]
noncomputable def lowerFace.exactFunctor :
    SimplicialObject A ⥤ₑ ChainComplex A ℕ :=
  ExactFunctor.of lowerFace

end CategoryTheory.Abelian.DoldKan.N

namespace CategoryTheory.SimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The intersection of the kernels of the lower face maps in degree `n`. It is the normalized
Moore subobject after reversing the simplex indexing. -/
@[stacks 017U "lower-face normalized Moore subobject",
  stacks 017V "lower-face normalized Moore subobject"]
def normalizedMoore.lowerFace.subobject (U : SimplicialObject A) (n : ℕ) :
    Subobject (U.obj (op ⦋n⦌)) :=
  NormalizedMooreComplex.objX (_root_.SimplicialObject.opFunctor.obj U) n

namespace normalizedMoore.lowerFace.subobject

/-- In degree zero, the lower-face normalized Moore subobject is the whole object. -/
@[simp, stacks 017U "degree-zero lower-face normalized Moore subobject",
  stacks 017V "degree-zero lower-face normalized Moore subobject"]
theorem zero (U : SimplicialObject A) :
    normalizedMoore.lowerFace.subobject U 0 = ⊤ := sorry

/-- In positive degree, the lower-face normalized Moore subobject is the intersection of the
kernels of `d₀, ..., dₙ`. -/
@[stacks 017U "positive-degree lower-face normalized Moore subobject",
  stacks 017V "positive-degree lower-face normalized Moore subobject"]
theorem add_one (U : SimplicialObject A) (n : ℕ) :
    normalizedMoore.lowerFace.subobject U (n + 1) =
      Finset.univ.inf (fun k : Fin (n + 1) ↦
        kernelSubobject (U.δ (Fin.castSucc k))) := sorry

/-- The map between lower-face normalized Moore subobjects induced by a simplicial morphism. -/
@[stacks 017U "functorial lower-face normalized Moore map",
  stacks 017V "functorial lower-face normalized Moore map"]
def map {U V : SimplicialObject A} (f : U ⟶ V) (n : ℕ) :
    (normalizedMoore.lowerFace.subobject U n : A) ⟶
      (normalizedMoore.lowerFace.subobject V n : A) :=
  ((Abelian.DoldKan.N.lowerFace (A := A)).map f).f n

namespace map

/-- The lower-face normalized Moore map commutes with the subobject inclusions. -/
@[reassoc, stacks 017U "lower-face map inclusion naturality",
  stacks 017V "lower-face map inclusion naturality"]
theorem arrow {U V : SimplicialObject A} (f : U ⟶ V) (n : ℕ) :
    normalizedMoore.lowerFace.subobject.map f n ≫
        (normalizedMoore.lowerFace.subobject V n).arrow =
      (normalizedMoore.lowerFace.subobject U n).arrow ≫ f.app (op ⦋n⦌) := sorry

/-- The lower-face normalized Moore map of an identity is the identity. -/
@[simp, stacks 017U "lower-face map identity", stacks 017V "lower-face map identity"]
theorem id (U : SimplicialObject A) (n : ℕ) :
    normalizedMoore.lowerFace.subobject.map (𝟙 U) n =
      𝟙 (normalizedMoore.lowerFace.subobject U n : A) := sorry

/-- Lower-face normalized Moore maps preserve composition. -/
@[stacks 017U "lower-face map composition", stacks 017V "lower-face map composition"]
theorem comp {U V W : SimplicialObject A}
    (f : U ⟶ V) (g : V ⟶ W) (n : ℕ) :
    normalizedMoore.lowerFace.subobject.map (f ≫ g) n =
      normalizedMoore.lowerFace.subobject.map f n ≫
        normalizedMoore.lowerFace.subobject.map g n := sorry

end map

end normalizedMoore.lowerFace.subobject

namespace normalizedMoore.lowerFace

/-- The subobject inequality identifying the lower-face differential with the restricted last
face map. -/
@[stacks 017X "last-face restriction construction"]
theorem lastFace.le_pullback (U : SimplicialObject A) (m : ℕ) :
    subobject U (m + 1) ≤
      (Subobject.pullback (U.δ (Fin.last (m + 1)))).obj (subobject U m) := sorry

/-- The lower-face normalized differential is the last face map restricted to consecutive
normalized subobjects. -/
@[stacks 017X "restricted last-face morphism"]
def lastFace (U : SimplicialObject A) (m : ℕ) :
    (subobject U (m + 1) : A) ⟶ (subobject U m : A) :=
  ((Abelian.DoldKan.N.lowerFace (A := A)).obj U).d (m + 1) m

/-- The restricted last face commutes with the inclusions of the lower-face normalized Moore
subobjects into the ambient simplicial object. -/
@[reassoc, stacks 017X "restricted last-face inclusion"]
theorem lastFace.arrow (U : SimplicialObject A) (m : ℕ) :
    lastFace U m ≫ (subobject U m).arrow =
      (subobject U (m + 1)).arrow ≫ U.δ (Fin.last (m + 1)) := sorry

end normalizedMoore.lowerFace

end CategoryTheory.SimplicialObject

namespace CategoryTheory.Abelian.DoldKan.N.lowerFace

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The object in degree `n` of the lower-face normalized Moore functor is the canonical
lower-face normalized subobject. -/
@[simp, stacks 017V "lower-face normalized Moore object formula"]
theorem obj_X (U : SimplicialObject A) (n : ℕ) :
    ((lowerFace (A := A)).obj U).X n =
      (CategoryTheory.SimplicialObject.normalizedMoore.lowerFace.subobject U n : A) := sorry

/-- The degree-`n` component of a lower-face normalized Moore map is the canonical map between
lower-face normalized subobjects. -/
@[simp, stacks 017V "lower-face normalized Moore map formula"]
theorem map_f {U V : SimplicialObject A} (f : U ⟶ V) (n : ℕ) :
    ((lowerFace (A := A)).map f).f n =
      CategoryTheory.SimplicialObject.normalizedMoore.lowerFace.subobject.map f n := sorry

/-- The differential of the lower-face normalized Moore functor is the restricted last face. -/
@[simp, stacks 017X "lower-face normalized Moore differential formula"]
theorem obj_d (U : SimplicialObject A) (m : ℕ) :
    ((lowerFace (A := A)).obj U).d (m + 1) m =
      CategoryTheory.SimplicialObject.normalizedMoore.lowerFace.lastFace U m := sorry

end CategoryTheory.Abelian.DoldKan.N.lowerFace
