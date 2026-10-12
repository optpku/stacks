/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.IrreducibleGenericPoint

@[expose] public section

universe u

/- Lemma 33.8.6 (1) (Tag 054Q): at a generic point of an irreducible scheme over a
field, geometric irreducibility is equivalent to that of its residue field. -/
@[stacks 054Q]
#check (AlgebraicGeometry.GeometricallyIrreducible.GenericPoint.iff_residueField :
  ∀ {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) [IrreducibleSpace X]
    (ξ : X) (hξ : ξ ∈ genericPoints X),
    AlgebraicGeometry.GeometricallyIrreducible f ↔
      AlgebraicGeometry.GeometricallyIrreducible
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (AlgebraicGeometry.Scheme.Hom.ResidueField.mapOfSpec f ξ))))

/- Lemma 33.8.6 (2) (Tag 054Q): the residue-field criterion is equivalent to
`separableClosure k (X.residueField ξ) = ⊥`. -/
@[stacks 054Q]
#check
  (AlgebraicGeometry.GeometricallyIrreducible.GenericPoint.ResidueField.iff_separableClosure_eq_bot :
    ∀ {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) [IrreducibleSpace X]
      (ξ : X) (hξ : ξ ∈ genericPoints X),
      AlgebraicGeometry.GeometricallyIrreducible
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
            (AlgebraicGeometry.Scheme.Hom.ResidueField.mapOfSpec f ξ))) ↔
        AlgebraicGeometry.Scheme.Hom.ResidueField.separableClosureOfSpec f ξ = ⊥)

end
