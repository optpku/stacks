module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Thickening
import StacksCheckRecall

/-!
# Open subspaces of thickenings of algebraic spaces

A thickening of algebraic spaces uniquely lifts open subspaces along the
closed subspace inclusion, recovering the original open as a fibre product.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.OpenSubspace

/- Lemma 76.9.3: Let `S` be a scheme. Let `i : X ⟶ X'` be a thickening of
algebraic spaces over `S`. For any open subspace `U ⊂ X` there exists a unique
open subspace `U' ⊂ X'` such that `U` is the fibre product `X ×_{X'} U'`. -/
@[stacks 05ZP] #check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.existsUnique_extend :
  ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsThickening i] (U : OpenSubspace X),
    ∃ U' : OpenSubspace X',
      (∃ g : U.X ⟶ U'.X, IsPullback U.ι g i U'.ι) ∧
        ∀ V' : OpenSubspace X',
          (∃ g : U.X ⟶ V'.X, IsPullback U.ι g i V'.ι) →
            ∃! φ : V'.X ≅ U'.X, φ.hom ≫ U'.ι = V'.ι)

end AlgebraicGeometry.AlgebraicSpace.OpenSubspace
