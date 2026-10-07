module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig.Fppf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped MorphismOfTopoiIn

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 59.100.1 (1): the canonical comparison identifies small-site global
sections with sections of the small-to-big inverse image. -/
@[stacks 0DDL]
#check (AlgebraicGeometry.Scheme.Etale.SmallToBig.sectionsComparison_bijective :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S)
      (F : Sheaf S.smallEtaleTopology (Type (u + 1))),
    Function.Bijective (Etale.SmallToBig.sectionsComparison f F))

/- Lemma 59.100.1 (2): the small-to-big inverse image is an fppf sheaf,
and hence is also an étale sheaf by its existing bundled inverse-image structure. -/
@[stacks 0DDL]
#check (AlgebraicGeometry.Scheme.Etale.SmallToBig.inverseImage_isSheaf_fppf :
    ∀ (S : Scheme.{u}) (F : Sheaf S.smallEtaleTopology (Type (u + 1))),
      Presheaf.IsSheaf (Scheme.fppfTopology.over S)
    (((Etale.SmallToBig.siteMorphismOfTopoi S)⁻¹).obj F).1)

/- Lemma 59.100.1 (3): the fppf inverse image is canonically identified
with the bundled fppf sheaf carried by the small-to-big inverse image. -/
@[stacks 0DDL]
#check (AlgebraicGeometry.Scheme.Etale.SmallToBig.toFppfInverseImageIso :
    ∀ (S : Scheme.{u}) (F : Sheaf S.smallEtaleTopology (Type (u + 1))),
      ((StandardTopology.toFppf .etale S)⁻¹).obj
          (((Etale.SmallToBig.siteMorphismOfTopoi S)⁻¹).obj F) ≅
    Etale.SmallToBig.inverseImageFppf S F)

end AlgebraicGeometry.Scheme
