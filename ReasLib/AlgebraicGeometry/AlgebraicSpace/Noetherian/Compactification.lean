module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Stratification.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ElementaryDistinguishedSquare
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.EtaleImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Affine étale enlargements of Noetherian algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A proper dense open subspace of a Noetherian algebraic space can be enlarged
by the image of an affine étale morphism to an elementary distinguished square
whose pullback over the original open subspace has dense image. -/
theorem exists_affineEtale_enlarging_elementaryDistinguishedSquare
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (U : OpenSubspace X) (h_dense : Dense U.pointsSet)
    (h_ne : U.pointsSet ≠ Set.univ) :
    ∃ (V : Over S) (f : ofOver V ⟶ X) (W : OpenSubspace X)
      (j : U.X ⟶ W.X) (fW : ofOver V ⟶ W.X),
      AlgebraicGeometry.IsAffine V.left ∧ Etale f ∧
        W.pointsSet = U.pointsSet ∪ Set.range (Points.map f) ∧
          j ≫ W.ι = U.ι ∧ fW ≫ W.ι = f ∧ U.pointsSet ⊂ W.pointsSet ∧
            IsElementaryDistinguishedSquare j fW ∧
              Dense (Set.range (Points.map (pullback.fst j fW))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
