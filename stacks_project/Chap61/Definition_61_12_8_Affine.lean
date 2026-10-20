module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Affine

/-!
# Affine bridge for Definition 61.12.8
-/

@[expose] public section

universe u v

/- Definition 61.12.8 -/
#check
  (AlgebraicGeometry.ChosenBigProetaleSite.bigAffineTopology :
    (X : AlgebraicGeometry.ChosenBigProetaleSite.{u, v}) →
      (S : X.carrier) →
        CategoryTheory.GrothendieckTopology
          (AlgebraicGeometry.ChosenBigProetaleSite.bigAffineSite X S))

/- Definition 61.12.8 -/
#check
  (AlgebraicGeometry.ChosenBigProetaleSite.bigAffineStandardCovering :
    (X : AlgebraicGeometry.ChosenBigProetaleSite.{u, v}) →
      (S : X.carrier) →
        {U : AlgebraicGeometry.ChosenBigProetaleSite.bigAffineSite X S} →
          CategoryTheory.Presieve U → Prop)

/- Definition 61.12.8 -/
#check
  (AlgebraicGeometry.ChosenBigProetaleSite.mem_bigAffineStandardPrecoverage_iff :
    (X : AlgebraicGeometry.ChosenBigProetaleSite.{u, v}) →
      (S : X.carrier) →
        {U : AlgebraicGeometry.ChosenBigProetaleSite.bigAffineSite X S} →
          {R : CategoryTheory.Presieve U} →
            R ∈ AlgebraicGeometry.ChosenBigProetaleSite.bigAffineStandardPrecoverage
              X S U ↔
                AlgebraicGeometry.ChosenBigProetaleSite.bigAffineStandardCovering
                  X S R)
