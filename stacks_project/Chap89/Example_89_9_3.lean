module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Modification.NonSchemes
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial

/- Example 89.9.3 -/
@[stacks 0AEB] #check (AlgebraicGeometry.AlgebraicSpace.exists_modification_not_scheme :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsNoetherianRing A) (_ : IsLocalRing A)
      (_ : IsExcellentRing A),
      ringKrullDim A = 2 ∧
        ∃ (X : AlgebraicSpace (Spec (.of A))) (f : X ⟶ AlgebraicGeometry.AlgebraicSpace.specSpace A)
          (_ : AlgebraicGeometry.AlgebraicSpace.IsIntegral X)
          (_ : AlgebraicGeometry.AlgebraicSpace.IsIntegral (AlgebraicGeometry.AlgebraicSpace.specSpace A)),
          AlgebraicGeometry.AlgebraicSpace.IsModification f ∧
            ¬ AlgebraicGeometry.AlgebraicSpace.IsScheme X)

#check (AlgebraicGeometry.AlgebraicSpace.exists_modification_not_scheme_localRing :
    ∃ (X : AlgebraicSpace (Spec (.of AlgebraicGeometry.CubicQuarticSurface.localRing)))
      (f : X ⟶ AlgebraicGeometry.AlgebraicSpace.specSpace AlgebraicGeometry.CubicQuarticSurface.localRing)
      (_ : AlgebraicGeometry.AlgebraicSpace.IsIntegral X)
      (_ : AlgebraicGeometry.AlgebraicSpace.IsIntegral
        (AlgebraicGeometry.AlgebraicSpace.specSpace AlgebraicGeometry.CubicQuarticSurface.localRing)),
      AlgebraicGeometry.AlgebraicSpace.IsModification f ∧
        ¬ AlgebraicGeometry.AlgebraicSpace.IsScheme X)
