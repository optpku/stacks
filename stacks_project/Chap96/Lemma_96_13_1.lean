module

public import ReasLib.CategoryTheory.Fibered.Groupoids.LocalEquivalence
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous
public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology

/-!
# Stackification and associated fppf sheaf topoi

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that induces
an equivalence of stackifications yields an equivalence of the associated fppf
sheaf topoi.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)

/-- Lemma 96.13.1: Let `f : X ⟶ Y` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. If `f` induces an equivalence of stackifications,
meaning `Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f`, then the
associated morphism of topoi `Sh(X.fppfTopology) ⟶ Sh(Y.fppfTopology)` is an
equivalence. -/
@[stacks 06WQ]
theorem fppfMorphismOfTopoi_isEquivalence
    (hf : Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f)
    [HasSheafify (X.p.inheritedTopology (Scheme.fppfTopology.over S)) (Type (u + 1))]
    [∀ P : X.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P] :
    ((toCartesianBasedFunctor f).morphismOfTopoiIn
        (Scheme.fppfTopology.over S)).inverseImage.IsEquivalence :=
  sorry

/-- A 1-morphism inducing an equivalence of stackifications is special
cocontinuous for the associated fppf sites. -/
theorem toFunctor_isSpecialCocontinuous
    (hf : Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f) :
    (toFunctor f).IsSpecialCocontinuous X.fppfTopology Y.fppfTopology :=
  sorry

/-- The cocontinuous direct image along such a 1-morphism is an equivalence of
fppf sheaf categories. -/
theorem sheafPushforwardCocontinuous_isEquivalence
    (hf : Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f)
    [HasSheafify (X.p.inheritedTopology (Scheme.fppfTopology.over S)) (Type (u + 1))]
    [∀ P : X.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P] :
    ((toCartesianBasedFunctor f).toFunctor.sheafPushforwardCocontinuous (Type (u + 1))
        X.fppfTopology Y.fppfTopology).IsEquivalence :=
  sorry

/-- Direct-image form of the associated fppf topos equivalence. -/
theorem fppfMorphismOfTopoi_pushforward_isEquivalence
    (hf : Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f)
    [HasSheafify (X.p.inheritedTopology (Scheme.fppfTopology.over S)) (Type (u + 1))]
    [∀ P : X.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P] :
    ((toCartesianBasedFunctor f).morphismOfTopoiIn
        (Scheme.fppfTopology.over S)).pushforward.IsEquivalence :=
  sorry

/-- Specialization of the topos equivalence to a stackification 1-morphism. -/
theorem fppfMorphismOfTopoi_isEquivalence_of_isStackification
    (hstack : Hom.IsStackification (Scheme.fppfTopology.over S) f)
    [HasSheafify (X.p.inheritedTopology (Scheme.fppfTopology.over S)) (Type (u + 1))]
    [∀ P : X.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P] :
    ((toCartesianBasedFunctor f).morphismOfTopoiIn
        (Scheme.fppfTopology.over S)).inverseImage.IsEquivalence :=
  sorry

end AlgebraicGeometry.GroupoidsOver
