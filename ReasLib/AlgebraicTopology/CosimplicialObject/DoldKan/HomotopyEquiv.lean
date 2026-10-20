module

public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.Homotopy
public import ReasLib.Algebra.Homology.Homotopy.Equiv

/-!
# Cosimplicial homotopy equivalences on normalized cochains

This leaf records both the structured and property-valued forms of preservation of homotopy
equivalences by the normalized cochain complex functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {U V : CosimplicialObject A} {a : U ⟶ V}

/-- The normalized cochain complex functor preserves the full morphism property of product-free
cosimplicial homotopy equivalences. -/
@[stacks 0FKK "normalized-cochain functor preserves homotopy equivalences"]
theorem homotopyEquivalences.normalizedCochain :
    homotopyEquivalences A ≤
      (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ)).inverseImage
        normalizedCochainComplex.functor := sorry

namespace HomotopyEquiv

/-- The normalized cochain complex of a product-free cosimplicial homotopy equivalence,
retaining the image of its chosen inverse. -/
@[stacks 0FKK "structured normalized-cochain homotopy equivalence"]
noncomputable def normalizedCochain (e : HomotopyEquiv U V) :
    HomRel.Equiv (homotopic A (ComplexShape.up ℕ))
      (normalizedCochainComplex.functor.obj U) (normalizedCochainComplex.functor.obj V) :=
  e.map normalizedCochainComplex.functor

namespace normalizedCochain

/-- The forward map of the normalized-cochain image is induced by the original forward
morphism. -/
@[simp, stacks 0FKK "normalized-cochain forward map formula"]
theorem hom (e : HomotopyEquiv U V) :
    e.normalizedCochain.hom = normalizedCochainComplex.functor.map e.hom := sorry

/-- The chosen inverse of the normalized-cochain image is induced by the original chosen
inverse. -/
@[simp, stacks 0FKK "normalized-cochain inverse map formula"]
theorem inv (e : HomotopyEquiv U V) :
    e.normalizedCochain.inv = normalizedCochainComplex.functor.map e.inv := sorry

/-- A product-free cosimplicial homotopy equivalence induces a chain homotopy equivalence on
normalized cochain complexes. -/
@[stacks 0FKK "normalized cochains preserve homotopy equivalences"]
theorem isHomotopyEquivalence (e : HomotopyEquiv U V) :
    HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ)
      (normalizedCochainComplex.functor.map e.hom) := sorry

end normalizedCochain

end HomotopyEquiv

/-- A product-free cosimplicial homotopy-equivalence morphism induces a chain homotopy
equivalence on normalized cochain complexes. -/
@[stacks 0FKK "normalized cochains preserve homotopy equivalences"]
theorem IsHomotopyEquivalence.normalizedCochain
    (ha : IsHomotopyEquivalence a) :
    HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ)
      (normalizedCochainComplex.functor.map a) := sorry

section Canonical

namespace homotopyEquivalences.degenerate

/-- The canonical normalized image functor preserves product-free cosimplicial homotopy
equivalences as chain-homotopy equivalences. -/
@[stacks 0FKK "canonical normalized image functor preserves homotopy equivalences"]
theorem normalized :
    homotopyEquivalences A ≤
      (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ)).inverseImage
        (DoldKan.degenerate.normalized.functor (A := A)) := sorry

end homotopyEquivalences.degenerate

namespace HomotopyEquiv.degenerate

/-- The canonical normalized image of a structured product-free cosimplicial homotopy equivalence,
retaining the chosen inverse. -/
@[stacks 0FKK "structured canonical normalized image homotopy equivalence"]
noncomputable def normalized (e : HomotopyEquiv U V) :
    HomRel.Equiv (homotopic A (ComplexShape.up ℕ))
      ((DoldKan.degenerate.normalized.functor (A := A)).obj U)
      ((DoldKan.degenerate.normalized.functor (A := A)).obj V) :=
  e.map (DoldKan.degenerate.normalized.functor (A := A))

namespace normalized

/-- The forward map of the canonical normalized image is induced by the original forward map. -/
@[simp, stacks 0FKK "canonical normalized image forward map"]
theorem hom (e : HomotopyEquiv U V) :
    (HomotopyEquiv.degenerate.normalized e).hom =
      (DoldKan.degenerate.normalized.functor (A := A)).map e.hom := sorry

/-- The chosen inverse of the canonical normalized image is induced by the original inverse. -/
@[simp, stacks 0FKK "canonical normalized image inverse map"]
theorem inv (e : HomotopyEquiv U V) :
    (HomotopyEquiv.degenerate.normalized e).inv =
      (DoldKan.degenerate.normalized.functor (A := A)).map e.inv := sorry

/-- A structured product-free cosimplicial homotopy equivalence induces a chain-homotopy
equivalence on the canonical normalized image quotient. -/
@[stacks 0FKK "canonical normalized image preserves homotopy equivalences"]
theorem isHomotopyEquivalence (e : HomotopyEquiv U V) :
    HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ)
      ((DoldKan.degenerate.normalized.functor (A := A)).map e.hom) := sorry

end normalized

end HomotopyEquiv.degenerate

namespace IsHomotopyEquivalence.degenerate

/-- A product-free cosimplicial homotopy-equivalence morphism induces a chain-homotopy
equivalence on the canonical normalized image quotient. -/
@[stacks 0FKK "canonical normalized image homotopy-equivalence morphism"]
theorem normalized (ha : IsHomotopyEquivalence a) :
    HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ)
      ((DoldKan.degenerate.normalized.functor (A := A)).map a) := sorry

end IsHomotopyEquivalence.degenerate

end Canonical

end CategoryTheory.CosimplicialObject
