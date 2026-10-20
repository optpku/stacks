module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldExtension.Galois
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support

/-!
# Intermediate projections of field-extension base changes

An intermediate field `K'` of a field extension `kbar / k` induces a projection
of fibre-product base changes `baseChange k kbar X ⟶ baseChange k K' X` over
`Spec k`. Open subspaces are compared by preimage of point-sets along this
projection.
-/

@[expose] public section

open CategoryTheory CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FieldExtension

/-- The canonical projection `baseChange k kbar X ⟶ baseChange k K' X` of
field-extension fibre products associated to an intermediate extension
`kbar / K' / k`. -/
def intermediateMap {k kbar : Type u} [Field k] [Field kbar] [Algebra k kbar]
    (K' : IntermediateField k kbar) (X : AlgebraicSpace (Spec (of k))) :
    baseChange k kbar X ⟶ baseChange k K' X :=
  productLift
    (baseChangeFst k kbar X ≫
      ofOverHomMk (AlgebraicGeometry.FieldExtension.specMap K' kbar)
        (AlgebraicGeometry.Scheme.AffineBaseChange.specMap_comp k K' kbar))
    (baseChangeSnd k kbar X)

/-- The intermediate projection acts as `Spec(K' → kbar)` on the `Spec` factor. -/
theorem intermediateMap_fst {k kbar : Type u} [Field k] [Field kbar] [Algebra k kbar]
    (K' : IntermediateField k kbar) (X : AlgebraicSpace (Spec (of k))) :
    intermediateMap K' X ≫ baseChangeFst k K' X =
      baseChangeFst k kbar X ≫
        ofOverHomMk (AlgebraicGeometry.FieldExtension.specMap K' kbar)
          (AlgebraicGeometry.Scheme.AffineBaseChange.specMap_comp k K' kbar) :=
  sorry

/-- The intermediate projection acts as the identity on the `X` factor. -/
theorem intermediateMap_snd {k kbar : Type u} [Field k] [Field kbar] [Algebra k kbar]
    (K' : IntermediateField k kbar) (X : AlgebraicSpace (Spec (of k))) :
    intermediateMap K' X ≫ baseChangeSnd k K' X = baseChangeSnd k kbar X :=
  sorry

/-- An open subspace of a field-extension base change is the preimage of an open
subspace from an intermediate extension. -/
def IsBaseChangeFromIntermediate {k kbar : Type u} [Field k] [Field kbar]
    [Algebra k kbar] (K' : IntermediateField k kbar)
    {X : AlgebraicSpace (Spec (of k))}
    (V : OpenSubspace (baseChange k kbar X))
    (V' : OpenSubspace (baseChange k K' X)) : Prop :=
  Points.map (intermediateMap K' X) ⁻¹' V'.pointsSet = V.pointsSet

/-- Intermediate descent of an open subspace is preimage of point-sets along the
canonical projection `baseChange k kbar X ⟶ baseChange k K' X`. -/
theorem IsBaseChangeFromIntermediate_iff {k kbar : Type u} [Field k] [Field kbar]
    [Algebra k kbar] (K' : IntermediateField k kbar)
    {X : AlgebraicSpace (Spec (of k))}
    (V : OpenSubspace (baseChange k kbar X))
    (V' : OpenSubspace (baseChange k K' X)) :
    IsBaseChangeFromIntermediate K' V V' ↔
      Points.map (intermediateMap K' X) ⁻¹' V'.pointsSet = V.pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FieldExtension
