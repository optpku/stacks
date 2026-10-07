module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Curve
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

/- Theorem 59.68.5: for a smooth curve over an algebraically closed field,
small-etale cohomology with coefficients in the multiplicative group sheaf is zero
in every degree `q ≥ 2`. -/
@[stacks 03RM] #check
  (AlgebraicGeometry.SchemeOverField.etaleUnitsCohomology_isZero :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.Curve X]
      [AlgebraicGeometry.Smooth X.hom]
      [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
      (q : Nat) (hq : 2 <= q),
      IsZero ((Sheaf.functorH X.left.smallEtaleTopology q).obj
        (AlgebraicGeometry.Scheme.Etale.Small.unitsAddSheaf X.left)))
