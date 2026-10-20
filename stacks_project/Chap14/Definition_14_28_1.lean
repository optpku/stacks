module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.Relation
import StacksCheckRecall

@[expose] public section

/-!
@stack 019W

# Source-facing bridge for Definition 14.28.1

Definition 14.28.1 defines cosimplicial homotopy between morphisms of cosimplicial objects.
The canonical owner declarations now live in the shared library module
`AlgebraicTopology.CosimplicialObject.Homotopy`.

This file re-exports those declarations and provides source-traceability checks.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe v u

-- Source traceability
namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]
variable {U V : CosimplicialObject C}
variable [HasFiniteProducts C]
variable (a b : U ⟶ V)
variable (H : CosimplicialObject.Homotopy a b)

/- Definition 14.28.1 (1): a cosimplicial homotopy is represented by a morphism into the
`Δ[1]` cotensor. -/
@[stacks 019W "Definition 14.28.1 (1): cotensor morphism"]
#check (H.hom : U ⟶ cotensor (Δ[1] : SSet.{0}) V)

/- Definition 14.28.1 (1): evaluation at the zero endpoint recovers `a`. -/
@[stacks 019W "Definition 14.28.1 (1): zero endpoint"]
#check (H.zero_endpoint :
  ∀ n : SimplexCategory,
    H.hom.app n ≫ Pi.π (fun _ ↦ V.obj n) (SSet.deltaOne.endpoint 0 (op n)) = a.app n)

/- Definition 14.28.1 (1): evaluation at the one endpoint recovers `b`. -/
@[stacks 019W "Definition 14.28.1 (1): one endpoint"]
#check (H.one_endpoint :
  ∀ n : SimplexCategory,
    H.hom.app n ≫ Pi.π (fun _ ↦ V.obj n) (SSet.deltaOne.endpoint 1 (op n)) = b.app n)

/- Definition 14.28.1 (2): the zigzag cosimplicial homotopy relation. -/
@[stacks 019W "Definition 14.28.1 (2)"]
#check (Iff.rfl :
  CosimplicialObject.Homotopic a b ↔
    Relation.EqvGen CosimplicialObject.DirectedHomotopy a b)

/- Reflexivity. -/
#check (CosimplicialObject.Homotopic.refl a)

end CategoryTheory.CosimplicialObject
