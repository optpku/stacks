module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig.Ph
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped MorphismOfTopoiIn

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 59.102.1: The small-to-big inverse image of a small étale sheaf
satisfies ph descent; it is already a bundled big étale sheaf. -/
@[stacks 0DDW] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.inverseImage_isSheaf_ph :
    ∀ (S : Scheme.{u}) (F : Sheaf S.smallEtaleTopology (Type (u + 1))),
      Presheaf.IsSheaf (Scheme.bigPhSite S)
        (((AlgebraicGeometry.Scheme.Etale.SmallToBig.siteMorphismOfTopoi S)⁻¹).obj F).1)

/- Lemma 59.102.1 (sections): The specified comparison identifies
Γ(X, f_small⁻¹ F) with the sections of π_S⁻¹ F over X. -/
@[stacks 0DDW] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.sectionsComparison_bijective :
    ∀ {S X : Scheme.{u}} (f : X ⟶ S)
      (F : Sheaf S.smallEtaleTopology (Type (u + 1))),
      Function.Bijective (AlgebraicGeometry.Scheme.Etale.SmallToBig.sectionsComparison f F))

/- Lemma 59.102.1 (ph identification): The canonical comparison unit
identifies π_S⁻¹ F with the restriction of ε_S⁻¹ π_S⁻¹ F. -/
@[stacks 0DDW] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.toPhInverseImageUnit_isIso :
    ∀ (S : Scheme.{u}) (F : Sheaf S.smallEtaleTopology (Type (u + 1))),
      IsIso ((AlgebraicGeometry.Scheme.PhComparison.standardComparison .etale S).adjunction.unit.app
        (((AlgebraicGeometry.Scheme.Etale.SmallToBig.siteMorphismOfTopoi S)⁻¹).obj F)))

end AlgebraicGeometry.Scheme
