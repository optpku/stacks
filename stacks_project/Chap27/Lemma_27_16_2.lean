module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.Affine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory Opposite
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

universe u

/- Lemma 27.16.2: in Situation 27.15.1, if `S` is affine, then the degree-`d`
functor associated to `(d, S, 𝒜)` is represented by the degree-`d` open subscheme of
`Proj(Γ(S, 𝒜))`. -/
@[stacks 01NU] #check
  (AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor.isRepresentedByTopSectionsDegreeOpen :
    ∀ {S : Scheme.{u}} (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) (d : ℕ)
      [𝒜.IsCommutative] [IsAffine S]
      (F_d : Scheme.RelativeProjDegreeFunctor S 𝒜 d)
      (associatedToQuadruples : F_d.IsAssociatedToQuadruples),
      ∃ x : F_d.toFunctor.obj
          (op (Proj.degreeOpen (RingedSpace.GradedAlgebraSections.grading 𝒜) d).toScheme),
        F_d.toFunctor.IsRepresentedBy x)
