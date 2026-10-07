module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.Characterizations

universe u

/- Remark 39.9.12: For a group scheme over a field, the sixteen combinations obtained by
choosing projective or proper, one of geometrically irreducible, irreducible, geometrically
connected, or connected, and smooth or geometrically reduced all characterize abelian
varieties. -/
@[stacks 0H2U] #check
  (AlgebraicGeometry.AbelianVariety.tfae :
    ∀ {k : Type u} [Field k] (A : AlgebraicGeometry.SchemeOverField k)
      [CategoryTheory.GrpObj A],
      List.TFAE
        [ AlgebraicGeometry.AbelianVariety A
        , AlgebraicGeometry.Projective A.hom ∧
            AlgebraicGeometry.GeometricallyIrreducible A.hom ∧ AlgebraicGeometry.Smooth A.hom
        , AlgebraicGeometry.Projective A.hom ∧
            AlgebraicGeometry.GeometricallyIrreducible A.hom ∧
              AlgebraicGeometry.GeometricallyReduced A.hom
        , AlgebraicGeometry.Projective A.hom ∧ IrreducibleSpace A.left ∧
            AlgebraicGeometry.Smooth A.hom
        , AlgebraicGeometry.Projective A.hom ∧ IrreducibleSpace A.left ∧
            AlgebraicGeometry.GeometricallyReduced A.hom
        , AlgebraicGeometry.Projective A.hom ∧
            AlgebraicGeometry.GeometricallyConnected A.hom ∧ AlgebraicGeometry.Smooth A.hom
        , AlgebraicGeometry.Projective A.hom ∧
            AlgebraicGeometry.GeometricallyConnected A.hom ∧
              AlgebraicGeometry.GeometricallyReduced A.hom
        , AlgebraicGeometry.Projective A.hom ∧ ConnectedSpace A.left ∧
            AlgebraicGeometry.Smooth A.hom
        , AlgebraicGeometry.Projective A.hom ∧ ConnectedSpace A.left ∧
            AlgebraicGeometry.GeometricallyReduced A.hom
        , AlgebraicGeometry.IsProper A.hom ∧
            AlgebraicGeometry.GeometricallyIrreducible A.hom ∧ AlgebraicGeometry.Smooth A.hom
        , AlgebraicGeometry.IsProper A.hom ∧
            AlgebraicGeometry.GeometricallyIrreducible A.hom ∧
              AlgebraicGeometry.GeometricallyReduced A.hom
        , AlgebraicGeometry.IsProper A.hom ∧ IrreducibleSpace A.left ∧
            AlgebraicGeometry.Smooth A.hom
        , AlgebraicGeometry.IsProper A.hom ∧ IrreducibleSpace A.left ∧
            AlgebraicGeometry.GeometricallyReduced A.hom
        , AlgebraicGeometry.IsProper A.hom ∧
            AlgebraicGeometry.GeometricallyConnected A.hom ∧ AlgebraicGeometry.Smooth A.hom
        , AlgebraicGeometry.IsProper A.hom ∧
            AlgebraicGeometry.GeometricallyConnected A.hom ∧
              AlgebraicGeometry.GeometricallyReduced A.hom
        , AlgebraicGeometry.IsProper A.hom ∧ ConnectedSpace A.left ∧
            AlgebraicGeometry.Smooth A.hom
        , AlgebraicGeometry.IsProper A.hom ∧ ConnectedSpace A.left ∧
            AlgebraicGeometry.GeometricallyReduced A.hom
        ])
