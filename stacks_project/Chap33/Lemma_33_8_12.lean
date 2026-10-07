module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.IrreducibleDenseResidueField

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat

universe u

/- Lemma 33.8.12 (Tag 0G69): an irreducible scheme over a field is geometrically irreducible
when the subset of points whose residue-field maps are isomorphisms is dense. -/
@[stacks 0G69]
#check
  (AlgebraicGeometry.GeometricallyIrreducible.ResidueField.of_irreducibleSpace_of_denseIsIsoMap :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)),
      IrreducibleSpace X →
        Dense ({x : X | CategoryTheory.IsIso (f.residueFieldMap x)} : Set X) →
          AlgebraicGeometry.GeometricallyIrreducible f)

end
