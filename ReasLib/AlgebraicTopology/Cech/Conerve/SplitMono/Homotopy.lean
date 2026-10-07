module

public import ReasLib.AlgebraicTopology.Cech.Conerve.SplitMono.Retraction
public import ReasLib.AlgebraicTopology.Cech.Conerve.Opposite.Iso
public import ReasLib.AlgebraicTopology.Cech.Nerve.SplitEpi.Homotopy
public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.Opposite
public import ReasLib.AlgebraicTopology.SimplicialSet.DeltaOne.Endpoint

@[expose] public section

/-!
@stack 019Z

# Homotopies of split Čech-conerve retractions

This module constructs the canonical product-free homotopy contracting the retraction-induced
endomorphism of a split Čech conerve.  Its components are transported from the split Čech-nerve homotopy of
the opposite arrow.  The mathematical API is layered under `SplitMono.cechConerve`; explicit
retraction data should normally be bundled with `SplitMono.mk`.
-/

open CategoryTheory
open CategoryTheory.Limits
open scoped Simplicial

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X Y : C} {f : X ⟶ Y}
variable [(Arrow.mk f).HasCechConerve]

namespace SplitMono

namespace cechConerve

namespace retractionEndomorphism

namespace opposite

/-- The split Čech-nerve contraction of the opposite arrow, reconstructed as a product-free
cosimplicial homotopy before transport across the Čech-conerve comparison. -/
@[stacks 019Z "opposite split Čech-nerve contraction"]
noncomputable def homotopy (r : SplitMono f) :
    CosimplicialObject.DeltaOneHomotopy
      (NatTrans.unop
        (SplitEpi.cechNerve.sectionEndomorphism.map (f := f.op) r.op))
      (NatTrans.unop (𝟙 (Arrow.mk f.op).cechNerve)) :=
  SimplicialObject.Homotopy.unop
    (SplitEpi.cechNerve.sectionEndomorphism.homotopy (f := f.op) r.op)

/-- Conjugating the opposite split-epimorphism endomorphism recovers the retraction-induced
endomorphism of the original Čech conerve. -/
@[stacks 019Z "opposite contraction source comparison"]
theorem conjugate_source (r : SplitMono f) :
    (Arrow.cechConerve.opposite.iso f).hom ≫
        NatTrans.unop
          (SplitEpi.cechNerve.sectionEndomorphism.map (f := f.op) r.op) ≫
      (Arrow.cechConerve.opposite.iso f).inv =
      SplitMono.cechConerve.retractionEndomorphism.map r := sorry

/-- Conjugating the identity of the unopposed opposite Čech nerve gives the identity of the
original Čech conerve, with the association used by `DeltaOneHomotopy.conjugate`. -/
@[stacks 019Z "opposite contraction identity comparison"]
theorem conjugate_identity :
    (Arrow.cechConerve.opposite.iso f).hom ≫
        NatTrans.unop (𝟙 (Arrow.mk f.op).cechNerve) ≫
      (Arrow.cechConerve.opposite.iso f).inv =
        𝟙 ((Arrow.mk f).cechConerve) := sorry

end opposite

namespace homotopy

/-- The component family obtained by conjugating the opposite Čech-nerve contraction across the
natural Čech-conerve comparison. -/
@[stacks 019Z "split Čech-conerve contraction components"]
noncomputable def component (r : SplitMono f) {n : SimplexCategory}
    (i : (Δ[1] : SSet).obj (Opposite.op n)) :
    (Arrow.mk f).cechConerve.obj n ⟶ (Arrow.mk f).cechConerve.obj n :=
  ((opposite.homotopy r).conjugate (Arrow.cechConerve.opposite.iso f)).hom i

/-- The conjugated contraction component is the opposite Čech-nerve component conjugated by
the natural comparison isomorphism. -/
@[simp, stacks 019Z "split Čech-conerve contraction component formula"]
theorem component.apply (r : SplitMono f) {n : SimplexCategory}
    (i : (Δ[1] : SSet).obj (Opposite.op n)) :
    component r i =
      (Arrow.cechConerve.opposite.iso f).hom.app n ≫
        (opposite.homotopy r).hom i ≫
          (Arrow.cechConerve.opposite.iso f).inv.app n := sorry

/-- The zero endpoint of the conjugated component family is the Čech-conerve retraction-induced
endomorphism. -/
@[stacks 019Z "split Cech-conerve contraction zero endpoint"]
theorem component.zero_endpoint (r : SplitMono f) (n : SimplexCategory) :
    component r (SSet.deltaOne.endpoint 0 (Opposite.op n)) =
      (SplitMono.cechConerve.retractionEndomorphism.map r).app n := sorry

/-- The one endpoint of the conjugated component family is the identity. -/
@[stacks 019Z "split Cech-conerve contraction one endpoint"]
theorem component.one_endpoint (r : SplitMono f) (n : SimplexCategory) :
    component r (SSet.deltaOne.endpoint 1 (Opposite.op n)) =
      (𝟙 ((Arrow.mk f).cechConerve) :
        (Arrow.mk f).cechConerve ⟶ (Arrow.mk f).cechConerve).app n := sorry

/-- The conjugated component family is natural in the simplex parameter. -/
@[stacks 019Z "split Cech-conerve contraction component naturality"]
theorem component.naturality (r : SplitMono f)
    {n₁ n₂ : SimplexCategory} (σ : n₁ ⟶ n₂)
    (i : (Δ[1] : SSet).obj (Opposite.op n₂)) :
    CommSq ((Arrow.mk f).cechConerve.map σ)
      (component r ((Δ[1] : SSet).map σ.op i))
      (component r i) ((Arrow.mk f).cechConerve.map σ) := sorry

end homotopy

/-- The canonical product-free homotopy from the Čech-conerve retraction-induced endomorphism of a split
monomorphism to the identity.  Its non-propositional component family is transported from the
split Čech-nerve homotopy of the opposite arrow. -/
@[stacks 019Z "split Čech-conerve contraction"]
noncomputable def homotopy (r : SplitMono f) :
    CosimplicialObject.DeltaOneHomotopy
      (SplitMono.cechConerve.retractionEndomorphism.map r)
      (𝟙 ((Arrow.mk f).cechConerve)) :=
  CosimplicialObject.DeltaOneHomotopy.cast
    (opposite.conjugate_source r)
    (opposite.conjugate_identity (f := f))
    ((opposite.homotopy r).conjugate (Arrow.cechConerve.opposite.iso f))

/-- The components of the split Čech-conerve contraction are the opposite Čech-nerve homotopy
components conjugated by the natural comparison isomorphism. -/
@[simp, stacks 019Z "split Čech-conerve contraction components"]
theorem homotopy.hom (r : SplitMono f) {n : SimplexCategory}
    (i : (Δ[1] : SSet).obj (Opposite.op n)) :
    (homotopy r).hom i =
      (Arrow.cechConerve.opposite.iso f).hom.app n ≫
        (opposite.homotopy r).hom i ≫
          (Arrow.cechConerve.opposite.iso f).inv.app n := sorry

/-- The retraction-induced Čech-conerve endomorphism of a split monomorphism is `Δ[1]`-homotopic to the
identity, as witnessed by `retractionEndomorphism.homotopy`. -/
@[stacks 019Z "split Čech-conerve contraction"]
theorem homotopic_id (r : SplitMono f) :
    CosimplicialObject.DeltaOneHomotopic
      (SplitMono.cechConerve.retractionEndomorphism.map r)
      (𝟙 ((Arrow.mk f).cechConerve)) := sorry

end retractionEndomorphism

namespace retraction

/-- The split Čech-conerve retraction followed by coaugmentation is `Δ[1]`-homotopic to the
identity. -/
@[stacks 019Z "split Čech-conerve retraction contraction"]
theorem comp_coaugmentation.homotopic_id (r : SplitMono f) :
    CosimplicialObject.DeltaOneHomotopic
      (SplitMono.cechConerve.retraction.hom r ≫ (Arrow.mk f).augmentedCechConerve.hom)
      (𝟙 ((Arrow.mk f).cechConerve)) := sorry

end retraction

namespace coaugmentation

/-- Canonical relation API for the coaugmentation followed by the retraction. -/
@[stacks 019Z "split Cech coaugmentation-retraction homotopy relation"]
theorem comp_retraction.homotopic_id (r : SplitMono f) :
    CosimplicialObject.DeltaOneHomotopic
      ((Arrow.mk f).augmentedCechConerve.hom ≫ SplitMono.cechConerve.retraction.hom r)
      (𝟙 ((CosimplicialObject.const C).obj X)) := sorry

/-- The Čech-conerve coaugmentation of a split monomorphism, equipped with its canonical
product-free cosimplicial homotopy inverse. -/
@[stacks 019Z "split Čech-conerve homotopy equivalence"]
noncomputable def homotopyEquiv (r : SplitMono f) :
    CosimplicialObject.HomotopyEquiv
      ((CosimplicialObject.const C).obj X) (Arrow.mk f).cechConerve where
  hom := (Arrow.mk f).augmentedCechConerve.hom
  inv := SplitMono.cechConerve.retraction.hom r
  hom_inv_id := comp_retraction.homotopic_id r
  inv_hom_id := retraction.comp_coaugmentation.homotopic_id r

/-- The forward map of the split Čech-conerve homotopy equivalence is its coaugmentation. -/
@[simp, stacks 019Z "forward map of the split Čech-conerve homotopy equivalence"]
theorem homotopyEquiv.hom (r : SplitMono f) :
    (homotopyEquiv r).hom = (Arrow.mk f).augmentedCechConerve.hom := sorry

/-- The inverse map of the split Čech-conerve homotopy equivalence is its canonical
retraction. -/
@[simp, stacks 019Z "inverse map of the split Čech-conerve homotopy equivalence"]
theorem homotopyEquiv.inv (r : SplitMono f) :
    (homotopyEquiv r).inv = SplitMono.cechConerve.retraction.hom r := sorry

/-- The Čech-conerve coaugmentation of a split monomorphism is a product-free cosimplicial
homotopy equivalence. -/
@[stacks 019Z "homotopy-equivalence property"]
theorem isHomotopyEquivalence (r : SplitMono f) :
    CosimplicialObject.IsHomotopyEquivalence (Arrow.mk f).augmentedCechConerve.hom := sorry

end coaugmentation

end cechConerve

end SplitMono

end CategoryTheory
