module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Projective
import StacksCheckRecall

universe u

/- Lemma 31.32.13 (1): the blowup of a scheme along a finite-type quasi-coherent ideal sheaf is
projective. -/
@[stacks 02NS] #check
  (AlgebraicGeometry.Blowup.projective_of_isFiniteType :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {I : X.IdealSheafData}
      (π : AlgebraicGeometry.Blowup X I) [I.toModule.IsQuasicoherent],
      I.IsFiniteType → AlgebraicGeometry.Projective π.hom)

/- Lemma 31.32.13 (2): the canonical degree-one Rees twist on such a blowup is relatively
ample, and hence invertible. -/
@[stacks 02NS] #check
  (AlgebraicGeometry.Blowup.twistOne_relativelyAmple_of_isFiniteType :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {I : X.IdealSheafData}
      (π : AlgebraicGeometry.Blowup X I) [I.toModule.IsQuasicoherent],
      I.IsFiniteType →
        AlgebraicGeometry.RelativelyAmple π.hom
          (π.reesPresentation.toRelativeProjPresentation.twist 1))
