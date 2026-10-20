module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig.H
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped MorphismOfTopoiIn

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 59.103.1: the small-to-big inverse image satisfies h descent.
The compared inverse image is already a bundled étale sheaf, so no separate
étale-sheaf theorem is needed. -/
@[stacks 0EW8] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.inverseImage_isSheaf_h :
    ∀ (S : Scheme.{u}) (F : Sheaf S.smallEtaleTopology (Type (u + 1))),
      Presheaf.IsSheaf (H.Big.site S)
        (((Etale.SmallToBig.siteMorphismOfTopoi S)⁻¹).obj F).1)

/- Lemma 59.103.1: the canonical comparison identifies global sections of
small étale pullback with sections of the big étale inverse image. -/
@[stacks 0EW8] #check (AlgebraicGeometry.Scheme.Etale.SmallToBig.sectionsComparison_bijective :
  ∀ {S X : Scheme.{u}} (f : X ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))),
    Function.Bijective (Etale.SmallToBig.sectionsComparison f F))

/- Lemma 59.103.1: the canonical h-sheafification unit identifies the
small-to-big inverse image with its h inverse image. -/
@[stacks 0EW8] #check (AlgebraicGeometry.Scheme.Etale.SmallToBig.toHInverseImageUnit_isIso :
  ∀ (S : Scheme.{u}) (F : Sheaf S.smallEtaleTopology (Type (u + 1))),
    IsIso ((HComparison.epsilon S).adjunction.unit.app
      (((Etale.SmallToBig.siteMorphismOfTopoi S)⁻¹).obj F)))

end AlgebraicGeometry.Scheme
