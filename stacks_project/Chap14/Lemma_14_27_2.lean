/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyEquiv.QuasiIso
import StacksCheckRecall

/-!
@stack 019T

# Source-facing recall for Lemma 14.27.2

The chain-homotopy-equivalence preservation APIs are owned by neutral
`ReasLib` leaves, independently of the Chapter 14 presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicTopology
open AlgebraicTopology.DoldKan

universe u v

namespace CategoryTheory.SimplicialObject

section AlternatingFace

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasFiniteBiproducts A]
variable {U V : SimplicialObject A} {a : U ⟶ V}
variable (ha : IsHomotopyEquivalence a) (e : HomotopyEquiv U V)

/- Lemma 14.27.2 (1): a simplicial homotopy equivalence induces a chain-homotopy equivalence
on alternating-face chain complexes. -/
@[stacks 019T "Lemma 14.27.2 (1)"]
#check (ha.alternatingFace :
  HomologicalComplex.homotopyEquivalences A (ComplexShape.down ℕ)
    ((alternatingFaceMapComplex A).map a))

/- The canonical owner also exposes preservation as an assumption-minimal inclusion of
morphism properties. -/
#check (homotopyEquivalences.alternatingFace (A := A) :
  homotopyEquivalences A ≤
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.down ℕ)).inverseImage
      (alternatingFaceMapComplex A))

/- The structured companion retains the chosen simplicial homotopy inverse. -/
#check (e.alternatingFace :
  HomRel.Equiv (homotopic A (ComplexShape.down ℕ))
    ((alternatingFaceMapComplex A).obj U) ((alternatingFaceMapComplex A).obj V))

section QuasiIso

variable [CategoryWithHomology A]

/- Canonical quasi-isomorphism consequence at the weaker category-with-homology layer. -/
#check (homotopyEquivalences.alternatingFace.le_quasiIso (A := A) :
  homotopyEquivalences A ≤
    (HomologicalComplex.quasiIso A (ComplexShape.down ℕ)).inverseImage
      (alternatingFaceMapComplex A))

end QuasiIso

end AlternatingFace

section NormalizedMoore

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {U V : SimplicialObject A} {a : U ⟶ V}
variable (ha : IsHomotopyEquivalence a) (e : HomotopyEquiv U V)

/- Lemma 14.27.2 (2): in an abelian category, a simplicial homotopy equivalence induces a
chain-homotopy equivalence on normalized Moore complexes. -/
@[stacks 019T "Lemma 14.27.2 (2)"]
#check (ha.normalizedMoore :
  HomologicalComplex.homotopyEquivalences A (ComplexShape.down ℕ)
    ((normalizedMooreComplex A).map a))

/- The canonical owner also exposes preservation as an inclusion of morphism properties. -/
#check (homotopyEquivalences.normalizedMoore (A := A) :
  homotopyEquivalences A ≤
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.down ℕ)).inverseImage
      (normalizedMooreComplex A))

/- The structured companion retains the chosen simplicial homotopy inverse. -/
#check (e.normalizedMoore :
  HomRel.Equiv (homotopic A (ComplexShape.down ℕ))
    ((normalizedMooreComplex A).obj U) ((normalizedMooreComplex A).obj V))

/- Canonical quasi-isomorphism consequence for normalized Moore complexes. -/
#check (homotopyEquivalences.normalizedMoore.le_quasiIso (A := A) :
  homotopyEquivalences A ≤
    (HomologicalComplex.quasiIso A (ComplexShape.down ℕ)).inverseImage
      (normalizedMooreComplex A))

end NormalizedMoore

end CategoryTheory.SimplicialObject
