module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 59.64.4: a sheaf of sets on the small étale site of a scheme is finite
locally constant exactly when it is represented by a finite étale scheme over the base. -/
@[stacks 03RV] #check
  (AlgebraicGeometry.Scheme.finiteLocallyConstant_iff_exists_finiteEtale :
    ∀ (X : Scheme.{u})
      [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
      (F : Sheaf X.smallEtaleTopology (Type (u + 1))),
      Sheaf.IsFiniteLocallyConstant F ↔
        ∃ (U : X.Etale), IsFinite U.hom ∧
          Nonempty (F ≅ X.smallEtaleTopology.sheafifiedRepresentable U))
