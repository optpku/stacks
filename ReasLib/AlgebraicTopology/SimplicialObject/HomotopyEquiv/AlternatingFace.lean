module

public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy.AlternatingFace
public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyEquiv
public import ReasLib.Algebra.Homology.Homotopy.Equiv
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Alternating-face complexes and simplicial homotopy equivalences

This leaf records that the alternating-face chain-complex functor sends
simplicial homotopy equivalences to chain-homotopy equivalences.
-/

@[expose] public section

open CategoryTheory
open AlgebraicTopology

universe u v

namespace CategoryTheory.SimplicialObject

variable {A : Type u} [Category.{v} A] [Preadditive A]
variable {U V : SimplicialObject A} {a : U ⟶ V}

/-- The alternating-face complex functor preserves the full morphism property of simplicial
homotopy equivalences. -/
@[stacks 019T "alternating-face functor preserves homotopy equivalences"]
theorem homotopyEquivalences.alternatingFace :
    homotopyEquivalences A ≤
      (HomologicalComplex.homotopyEquivalences A (ComplexShape.down ℕ)).inverseImage
        (alternatingFaceMapComplex A) := sorry

namespace HomotopyEquiv

/-- The alternating-face complex of a simplicial homotopy equivalence, retaining the image of
its chosen inverse. -/
@[stacks 019T "structured alternating-face homotopy equivalence"]
noncomputable def alternatingFace (e : HomotopyEquiv U V) :
    HomRel.Equiv (homotopic A (ComplexShape.down ℕ))
      ((alternatingFaceMapComplex A).obj U) ((alternatingFaceMapComplex A).obj V) :=
  e.map (alternatingFaceMapComplex A)

namespace alternatingFace

/-- The forward map of the alternating-face image is the alternating-face map of the original
forward morphism. -/
@[simp, stacks 019T "alternating-face homotopy-equivalence forward map"]
theorem hom (e : HomotopyEquiv U V) :
    e.alternatingFace.hom = (alternatingFaceMapComplex A).map e.hom := sorry

/-- The chosen inverse of the alternating-face image is the alternating-face map of the original
chosen inverse. -/
@[simp, stacks 019T "alternating-face homotopy-equivalence inverse map"]
theorem inv (e : HomotopyEquiv U V) :
    e.alternatingFace.inv = (alternatingFaceMapComplex A).map e.inv := sorry

/-- A simplicial homotopy equivalence induces a chain-homotopy equivalence on alternating-face
complexes. -/
@[stacks 019T "alternating-face homotopy equivalence"]
theorem isHomotopyEquivalence (e : HomotopyEquiv U V) :
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.down ℕ))
      ((alternatingFaceMapComplex A).map e.hom) := sorry

end alternatingFace

end HomotopyEquiv

namespace IsHomotopyEquivalence

/-- A simplicial homotopy-equivalence morphism induces a chain-homotopy equivalence on
alternating-face complexes. -/
@[stacks 019T "alternating-face homotopy-equivalence morphism"]
theorem alternatingFace (ha : IsHomotopyEquivalence a) :
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.down ℕ))
      ((alternatingFaceMapComplex A).map a) := sorry

end IsHomotopyEquivalence

end CategoryTheory.SimplicialObject
