module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.AlternatingCoface
public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.HomotopyEquiv
public import Mathlib.Algebra.Homology.QuasiIso

/-!
@stack 0FKK

# Cosimplicial homotopy equivalences and quasi-isomorphisms

Alternating coface and normalized cochain complexes carry product-free cosimplicial homotopy
equivalences to chain-homotopy equivalences. The canonical inclusion of that morphism property
into quasi-isomorphisms gives property-level, structured, and pointwise consumer APIs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open AlgebraicTopology

universe u v

namespace CategoryTheory.CosimplicialObject

variable {A : Type u} [Category.{v} A]
variable {U V : CosimplicialObject A} {f : U ⟶ V}

section AlternatingCoface

variable [Preadditive A] [CategoryWithHomology A]

namespace homotopyEquivalences.alternatingCoface

/-- Product-free cosimplicial homotopy equivalences lie in the inverse image of
quasi-isomorphisms under the alternating-coface complex functor. -/
@[stacks 0FKK "alternating-coface complexes send homotopy equivalences to quasi-isomorphisms"]
theorem le_quasiIso :
    homotopyEquivalences A ≤
      (HomologicalComplex.quasiIso A (ComplexShape.up ℕ)).inverseImage
        (alternatingCofaceMapComplex A) := sorry

end homotopyEquivalences.alternatingCoface

namespace HomotopyEquiv.alternatingCoface

/-- A structured product-free cosimplicial homotopy equivalence induces a quasi-isomorphism on
alternating-coface complexes. -/
@[stacks 0FKK "structured alternating-coface homotopy-equivalence quasi-isomorphism"]
instance quasiIso (e : HomotopyEquiv U V) :
    QuasiIso ((alternatingCofaceMapComplex A).map e.hom) := sorry

end HomotopyEquiv.alternatingCoface

/-- A product-free cosimplicial homotopy-equivalence morphism induces a quasi-isomorphism on
alternating-coface complexes. -/
@[stacks 0FKK "alternating-coface homotopy-equivalence quasi-isomorphism"]
theorem IsHomotopyEquivalence.alternatingCoface.quasiIso
    (hf : IsHomotopyEquivalence f) :
    QuasiIso ((alternatingCofaceMapComplex A).map f) := sorry

end AlternatingCoface

section NormalizedCochain

variable [Abelian A]

namespace homotopyEquivalences.normalizedCochain

/-- Product-free cosimplicial homotopy equivalences lie in the inverse image of
quasi-isomorphisms under the normalized cochain complex functor. -/
@[stacks 0FKK "normalized cochains send homotopy equivalences to quasi-isomorphisms"]
theorem le_quasiIso :
    homotopyEquivalences A ≤
      (HomologicalComplex.quasiIso A (ComplexShape.up ℕ)).inverseImage
        normalizedCochainComplex.functor := sorry

end homotopyEquivalences.normalizedCochain

namespace HomotopyEquiv.normalizedCochain

/-- A structured product-free cosimplicial homotopy equivalence induces a quasi-isomorphism on
normalized cochain complexes. -/
@[stacks 0FKK "structured normalized-cochain homotopy-equivalence quasi-isomorphism"]
instance quasiIso (e : HomotopyEquiv U V) :
    QuasiIso (normalizedCochainComplex.functor.map e.hom) := sorry

end HomotopyEquiv.normalizedCochain

/-- A product-free cosimplicial homotopy-equivalence morphism induces a quasi-isomorphism on
normalized cochain complexes. -/
@[stacks 0FKK "normalized-cochain homotopy-equivalence quasi-isomorphism"]
theorem IsHomotopyEquivalence.normalizedCochain.quasiIso
    (hf : IsHomotopyEquivalence f) :
    QuasiIso (normalizedCochainComplex.functor.map f) := sorry

end NormalizedCochain

section Canonical

variable [Abelian A]
namespace homotopyEquivalences.degenerate.normalized

/-- Lemma 14.28.7: the canonical normalized image functor sends product-free cosimplicial
homotopy equivalences to quasi-isomorphisms. -/
@[stacks 0FKK "canonical normalized image homotopy-equivalence quasi-isomorphism"]
theorem le_quasiIso :
    homotopyEquivalences A ≤
      (HomologicalComplex.quasiIso A (ComplexShape.up ℕ)).inverseImage
        (DoldKan.degenerate.normalized.functor (A := A)) := sorry

end homotopyEquivalences.degenerate.normalized

namespace HomotopyEquiv.degenerate.normalized

/-- A structured product-free cosimplicial homotopy equivalence induces a quasi-isomorphism on
the canonical normalized image quotient. -/
@[stacks 0FKK "structured canonical normalized image quasi-isomorphism"]
instance quasiIso (e : HomotopyEquiv U V) :
    QuasiIso ((DoldKan.degenerate.normalized.functor (A := A)).map e.hom) := sorry

end HomotopyEquiv.degenerate.normalized

namespace IsHomotopyEquivalence.degenerate.normalized

/-- A product-free cosimplicial homotopy-equivalence morphism induces a quasi-isomorphism on the
canonical normalized image quotient. -/
@[stacks 0FKK "canonical normalized image homotopy-equivalence quasi-isomorphism"]
theorem quasiIso (hf : IsHomotopyEquivalence f) :
    QuasiIso ((DoldKan.degenerate.normalized.functor (A := A)).map f) := sorry

end IsHomotopyEquivalence.degenerate.normalized

end Canonical

end CategoryTheory.CosimplicialObject
