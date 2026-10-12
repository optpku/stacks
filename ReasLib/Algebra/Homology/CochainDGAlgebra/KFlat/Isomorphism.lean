/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat.Isomorphism
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom
public import ReasLib.Algebra.Homology.CochainDGAlgebra.KFlat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism Transport for K-Flat Cochain Differential Graded Algebras

K-flatness of a cochain differential graded algebra depends only on the isomorphism class of its
underlying cochain complex.  This leaf exposes that transport without importing degree-zero or
monoidal compatibility results.
@stack 06XZ
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CochainDGAlgebra

variable {R : Type u} [CommRing R]

namespace IsKFlat

/-- K-flatness transports from the source to the target of an isomorphism of cochain differential
graded algebras. -/
theorem of_iso {A B : CochainDGAlgebra.{u, v} R} (hA : A.IsKFlat) (e : A ≅ B) :
    B.IsKFlat := sorry

/-- Isomorphic cochain differential graded algebras are simultaneously K-flat over the ground
ring. -/
@[stacks 06XZ "isomorphism invariance of K-flat cochain differential graded algebras"]
theorem iff_of_iso {A B : CochainDGAlgebra.{u, v} R} (e : A ≅ B) :
    A.IsKFlat ↔ B.IsKFlat := sorry

end IsKFlat

end CochainDGAlgebra
