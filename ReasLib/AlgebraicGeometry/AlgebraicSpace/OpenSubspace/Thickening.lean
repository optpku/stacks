module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Open subspaces of thickenings of algebraic spaces

Open subspaces extend uniquely along thickenings, up to unique isomorphism over
the ambient algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.OpenSubspace

/-- Every open subspace of an algebraic space is the pullback of an open subspace
along a thickening, unique up to unique isomorphism over the thickened space. -/
theorem existsUnique_extend {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsThickening i] (U : OpenSubspace X) :
    ∃ U' : OpenSubspace X',
      (∃ g : U.X ⟶ U'.X, IsPullback U.ι g i U'.ι) ∧
        ∀ V' : OpenSubspace X',
          (∃ g : U.X ⟶ V'.X, IsPullback U.ι g i V'.ι) →
            ∃! φ : V'.X ≅ U'.X, φ.hom ≫ U'.ι = V'.ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.OpenSubspace
