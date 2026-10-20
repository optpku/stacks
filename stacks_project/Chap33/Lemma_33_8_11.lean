module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.IrreducibleComponents
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits CommRingCat
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

noncomputable section

/- The source projection sends an irreducible component of a field-extension base change to an
irreducible component of the original scheme. -/
#check (AlgebraicGeometry.FieldExtension.Irreducible.image_component :
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (T : irreducibleComponents (FieldExtension.baseChange k K f)),
    (FieldExtension.toSource k K f).base ''
        (T : Set (FieldExtension.baseChange k K f)) ∈ irreducibleComponents X)

/- The images under the source projection define the canonical map on irreducible components. -/
#check (AlgebraicGeometry.FieldExtension.Irreducible.componentsMap :
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)),
    irreducibleComponents (FieldExtension.baseChange k K f) → irreducibleComponents X)

/- The canonical component map sends a component to its image under the source projection. -/
#check (AlgebraicGeometry.FieldExtension.Irreducible.coe_componentsMap :
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (T : irreducibleComponents (FieldExtension.baseChange k K f)),
    ((FieldExtension.Irreducible.componentsMap k K f T : irreducibleComponents X) : Set X) =
      (FieldExtension.toSource k K f).base ''
        (T : Set (FieldExtension.baseChange k K f)))

/- Lemma 33.8.11: for a field-extension base change, the source projection sends each
irreducible component to an irreducible component and induces a surjection on components. -/
@[stacks 04KX] #check
  (AlgebraicGeometry.FieldExtension.Irreducible.componentsMap_surjective :
    ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)),
      Function.Surjective (AlgebraicGeometry.FieldExtension.Irreducible.componentsMap k K f))

end

end AlgebraicGeometry
