/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap84.Lemma_84_5_1_Comparison
import StacksCheckRecall

/-!
# Lemma 84.5.1

For a sheaf of sets `F` on the small étale site of an algebraic space `X`,
inverse image along `π_X` is identified objectwise with global sections of
small-site pullback, and the same presheaf is a sheaf for smooth, syntomic,
fppf, fpqc, and ph coverings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open scoped MorphismOfTopoiIn

universe u

/- Lemma 84.5.1 (1): inverse image along `π_X` is given by
`(π_X⁻¹ F)(Y) = Γ(Y_étale, f_small⁻¹ F)` for `f : Y ⟶ X` in `(Spaces/X)_étale`. -/
@[stacks 0DG7] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.sectionsComparison_bijective :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
      (F : Sheaf (smallEtaleTopology X) (Type (u + 1))),
      Function.Bijective (sectionsComparison f F))

/- Lemma 84.5.1 (2): `π_X⁻¹ F` satisfies the sheaf condition for smooth coverings. -/
@[stacks 0DG7] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.inverseImage_isSheaf_smooth :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (F : Sheaf (smallEtaleTopology X) (Type (u + 1))),
      Presheaf.IsSheaf ((smoothPrecoverage S).toGrothendieck.over X)
        (((siteMorphismOfTopoi X)⁻¹).obj F).1)

/- Lemma 84.5.1 (3): `π_X⁻¹ F` satisfies the sheaf condition for syntomic coverings. -/
@[stacks 0DG7] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.inverseImage_isSheaf_syntomic :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (F : Sheaf (smallEtaleTopology X) (Type (u + 1))),
      Presheaf.IsSheaf ((syntomicPrecoverage S).toGrothendieck.over X)
        (((siteMorphismOfTopoi X)⁻¹).obj F).1)

/- Lemma 84.5.1 (4): `π_X⁻¹ F` satisfies the sheaf condition for fppf coverings. -/
@[stacks 0DG7] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.inverseImage_isSheaf_fppf :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (F : Sheaf (smallEtaleTopology X) (Type (u + 1))),
      Presheaf.IsSheaf (overFppfTopology X)
        (((siteMorphismOfTopoi X)⁻¹).obj F).1)

/- Lemma 84.5.1 (5): `π_X⁻¹ F` satisfies the sheaf condition for fpqc coverings. -/
@[stacks 0DG7] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.inverseImage_isSheaf_fpqc :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (F : Sheaf (smallEtaleTopology X) (Type (u + 1))),
      Presheaf.IsSheaf (overFpqcTopology X)
        (((siteMorphismOfTopoi X)⁻¹).obj F).1)

/- Lemma 84.5.1 (6): `π_X⁻¹ F` satisfies the sheaf condition for ph coverings. -/
@[stacks 0DG7] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.inverseImage_isSheaf_ph :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (F : Sheaf (smallEtaleTopology X) (Type (u + 1))),
      Presheaf.IsSheaf (bigPhSite X)
        (((siteMorphismOfTopoi X)⁻¹).obj F).1)

end
