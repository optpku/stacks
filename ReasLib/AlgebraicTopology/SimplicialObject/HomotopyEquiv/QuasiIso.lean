/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyEquiv.AlternatingFace
public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyEquiv.NormalizedMoore
public import Mathlib.Algebra.Homology.QuasiIso

/-!
@stack 019T

# Simplicial homotopy equivalences and quasi-isomorphisms

The alternating-face and normalized Moore complexes send a simplicial homotopy equivalence to a
chain-homotopy equivalence.  The standard chain-complex morphism-property inclusion then makes
both images quasi-isomorphisms.
-/

@[expose] public section

open CategoryTheory HomologicalComplex
open AlgebraicTopology

universe u v

namespace CategoryTheory.SimplicialObject

variable {A : Type u} [Category.{v} A]
variable {U V : SimplicialObject A} {f : U ⟶ V}

section AlternatingFace

variable [Preadditive A] [CategoryWithHomology A]

namespace homotopyEquivalences.alternatingFace

/-- Simplicial homotopy equivalences lie in the inverse image of chain-complex
quasi-isomorphisms under the alternating-face complex functor. -/
@[stacks 019T "alternating-face complexes send homotopy equivalences to quasi-isomorphisms"]
theorem le_quasiIso :
    homotopyEquivalences A ≤
      (HomologicalComplex.quasiIso A (ComplexShape.down ℕ)).inverseImage
        (alternatingFaceMapComplex A) := sorry

end homotopyEquivalences.alternatingFace

namespace HomotopyEquiv

namespace alternatingFace

/-- A structured simplicial homotopy equivalence induces a quasi-isomorphism on alternating-face
complexes. -/
@[stacks 019T "structured alternating-face homotopy-equivalence quasi-isomorphism"]
instance quasiIso (e : HomotopyEquiv U V) :
    QuasiIso ((alternatingFaceMapComplex A).map e.hom) := sorry

end alternatingFace

end HomotopyEquiv

/-- A simplicial homotopy-equivalence morphism induces a quasi-isomorphism on alternating-face
complexes. -/
@[stacks 019T "alternating-face homotopy-equivalence quasi-isomorphism"]
theorem IsHomotopyEquivalence.alternatingFace.quasiIso (hf : IsHomotopyEquivalence f) :
    QuasiIso ((alternatingFaceMapComplex A).map f) := sorry

end AlternatingFace

section NormalizedMoore

variable [Abelian A]

namespace homotopyEquivalences.normalizedMoore

/-- Simplicial homotopy equivalences lie in the inverse image of chain-complex
quasi-isomorphisms under the normalized Moore complex functor. -/
@[stacks 019T "normalized Moore complexes send homotopy equivalences to quasi-isomorphisms"]
theorem le_quasiIso :
    homotopyEquivalences A ≤
      (HomologicalComplex.quasiIso A (ComplexShape.down ℕ)).inverseImage
        (normalizedMooreComplex A) := sorry

end homotopyEquivalences.normalizedMoore

namespace HomotopyEquiv

namespace normalizedMoore

/-- A structured simplicial homotopy equivalence induces a quasi-isomorphism on normalized Moore
complexes. -/
@[stacks 019T "structured homotopy-equivalence quasi-isomorphism"]
instance quasiIso (e : HomotopyEquiv U V) :
    QuasiIso ((normalizedMooreComplex A).map e.hom) := sorry

end normalizedMoore

end HomotopyEquiv

/-- A simplicial homotopy-equivalence morphism induces a quasi-isomorphism on normalized Moore
complexes. -/
@[stacks 019T "homotopy-equivalence quasi-isomorphism"]
theorem IsHomotopyEquivalence.normalizedMoore.quasiIso (hf : IsHomotopyEquivalence f) :
    QuasiIso ((normalizedMooreComplex A).map f) := sorry

end NormalizedMoore

end CategoryTheory.SimplicialObject
