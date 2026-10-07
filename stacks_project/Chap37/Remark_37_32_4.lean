module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Bertini
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped ENat

noncomputable section

universe u

/- Remark 37.32.4: over an algebraically closed field, a smooth irreducible scheme of
dimension at least two with a closed immersion into projective space has a hyperplane whose
scheme-theoretic intersection with it is smooth and irreducible. -/
@[stacks 0G4G] #check
  (AlgebraicGeometry.ProjectivePresentation.exists_smooth_irreducible_hyperplaneSection :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
      (X : Over (Spec (CommRingCat.of k))) [Smooth X.hom] [IrreducibleSpace X.left]
      (P : ProjectiveSpaceOver (Spec (CommRingCat.of k)) n) (i : X.left ⟶ P.scheme)
      (h_i : ProjectivePresentation X.hom P.hom i)
      (h_dim : (2 : WithBot ℕ∞) ≤ topologicalKrullDim X.left),
      ∃ (H : Scheme.{u}) (j : H ⟶ P.scheme),
        ProjectiveSpaceHyperplane P j ∧
          (Smooth (Limits.pullback.fst i j ≫ X.hom) ∧
            IrreducibleSpace (Limits.pullback i j : Scheme.{u})))
