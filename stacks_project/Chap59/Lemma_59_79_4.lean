module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ClosedImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale AlgebraicGeometry.Scheme.Etale.ClosedImmersion

universe u

/- Lemma 59.79.4 (1): exact small-étale direct image agrees with every total
right-derived model of that functor. -/
@[stacks 0AEG] #check
  (AlgebraicGeometry.Scheme.Etale.ClosedImmersion.derivedDirectImageModelIso :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      [HasDerivedCategory.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [HasDerivedCategory.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
      (model : RightDerivedModel (abelianDirectImage i)),
      model.functor ≅ derivedDirectImage i)

/- Lemma 59.79.4 (2): derived small-étale direct image induces the equivalence
`D(Z_étale) ⥤ D_Z(X_étale)`. -/
@[stacks 0AEG] #check
  (AlgebraicGeometry.Scheme.Etale.ClosedImmersion.derivedDirectImage.toSupported_isEquivalence :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      [HasDerivedCategory.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [HasDerivedCategory.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})],
      (derivedDirectImage.toSupported i).IsEquivalence)

/- Lemma 59.79.4 (3): restricted small-étale inverse image is the quasi-inverse
of the supported direct-image equivalence. -/
@[stacks 0AEG] #check
  (AlgebraicGeometry.Scheme.Etale.ClosedImmersion.supportedQuasiInverse :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      [HasDerivedCategory.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [HasDerivedCategory.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})],
      (derivedDirectImage.toSupported i).inv ≅
        DerivedSupported.inclusion i ⋙ (abelianInverseImage i).mapDerivedCategory)

/- Lemma 59.79.4 (4): on supported derived objects, inverse image agrees with
the genuine total right-derived functor of concrete sections with support. -/
@[stacks 0AEG] #check
  (AlgebraicGeometry.Scheme.Etale.ClosedImmersion.supportedSectionsQuasiInverseIso :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      [HasDerivedCategory.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [HasDerivedCategory.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})],
      DerivedSupported.inclusion i ⋙ (abelianInverseImage i).mapDerivedCategory ≅
        DerivedSupported.inclusion i ⋙ derivedSectionsWithSupport i)
