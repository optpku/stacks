module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.SheafEquivalence
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 96.13.1: Let `f : X ⟶ Y` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. If `f` induces an equivalence of stackifications,
meaning `Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f`, then the
associated morphism of topoi `Sh(X.fppfTopology) ⟶ Sh(Y.fppfTopology)` is an
equivalence. -/
@[stacks 06WQ] #check
  (AlgebraicGeometry.GroupoidsOver.fppfMorphismOfTopoi_isEquivalence :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
      (hf : Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f),
      (((toCartesianBasedFunctor f).morphismOfTopoiIn
          (Scheme.fppfTopology.over S)).inverseImage :
        Sheaf Y.fppfTopology (Type (u + 1)) ⥤
          Sheaf X.fppfTopology (Type (u + 1))).IsEquivalence)
