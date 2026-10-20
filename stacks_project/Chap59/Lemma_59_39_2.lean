module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.SmallToBig.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig.Sections
public import stacks_project.Chap59.Lemma_59_39_1
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped MorphismOfTopoiIn

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 59.39.2 (1): Zariski inverse-image sections are canonically identified
with global sections of small-site pullback. -/
@[stacks 09XN] #check
  (AlgebraicGeometry.Scheme.Zariski.SmallToBig.sectionsComparison_bijective :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S)
      (F : Sheaf S.smallZariskiTopology (Type (u + 1))),
      Function.Bijective (AlgebraicGeometry.Scheme.Zariski.SmallToBig.sectionsComparison f F))

/- Lemma 59.39.2 (2): Étale inverse-image sections are canonically identified
with global sections of small-site pullback. -/
@[stacks 09XN] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.sectionsComparison_bijective :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S)
      (F : Sheaf S.smallEtaleTopology (Type (u + 1))),
      Function.Bijective (AlgebraicGeometry.Scheme.Etale.SmallToBig.sectionsComparison f F))

/- Lemma 59.39.2 (3): Small-to-big Zariski inverse image satisfies fpqc descent. -/
@[stacks 09XN] #check
  (AlgebraicGeometry.Scheme.Zariski.SmallToBig.inverseImage_isSheaf_fpqc :
    ∀ (S : Scheme.{u}) (F : Sheaf S.smallZariskiTopology (Type (u + 1))),
      Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
        (((AlgebraicGeometry.Scheme.Zariski.SmallToBig.siteMorphismOfTopoi S)⁻¹).obj F).1)

/- Lemma 59.39.2 (4): Small-to-big étale inverse image satisfies fpqc descent. -/
@[stacks 09XN] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.inverseImage_isSheaf_fpqc :
    ∀ (S : Scheme.{u}) (F : Sheaf S.smallEtaleTopology (Type (u + 1))),
      Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
        (((AlgebraicGeometry.Scheme.Etale.SmallToBig.siteMorphismOfTopoi S)⁻¹).obj F).1)

end AlgebraicGeometry.Scheme
