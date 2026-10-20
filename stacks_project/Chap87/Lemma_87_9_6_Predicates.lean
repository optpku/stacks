module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.McQuillan.Criteria

/-!
# McQuillan predicate specifications

Typed specifications of the formal-spectrum and closed-immersion criteria.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite
open AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.IsAffineFormalAlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}}
  [HasWeakSheafify (full.bigTopology S) (Type (u + 1))]
  [HasPullbacks (Sheaf (full.bigTopology S) (Type (u + 1)))]
  (X : Sheaf (full.bigTopology S) (Type (u + 1)))

/- Lemma 87.9.6: predicate specification. -/
#check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.isColimitOfWeakIdealSpectrum_iff X :
  isColimitOfWeakIdealSpectrum X ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : TopologicalRing.IsWeaklyAdmissibleRing A)
        (structureHom : Spec (.of A) ⟶ S),
        Nonempty (X ≅ FppfFormalSpectrum.spf A structureHom))

/- Lemma 87.9.6: predicate specification. -/
#check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.hasAffineClosedImmersionToSpec_iff X :
  hasAffineClosedImmersionToSpec X ↔
      IsAffineFormalAlgebraicSpace X ∧
        ∃ (A : Type u) (_ : CommRing A) (structureHom : Spec (.of A) ⟶ S)
          (f : X ⟶ (full.bigTopology S).sheafifiedRepresentable (Over.mk structureHom)),
          ∀ (T : full.bigAffineSite S)
            (t : (full.bigTopology S).sheafifiedRepresentable
              ((full.bigAffineInclusion S).obj T) ⟶ X),
            (MorphismProperty.inverseImage (@IsClosedImmersion) (full.bigToScheme S)).relative
                (full.bigTopology S).sheafifiedRepresentableFunctor t →
              (MorphismProperty.inverseImage (@IsClosedImmersion) (full.bigToScheme S)).relative
                (full.bigTopology S).sheafifiedRepresentableFunctor (t ≫ f))

/- Lemma 87.9.6: predicate specification. -/
#check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.hasSchemeClosedImmersionToSpec_iff X :
  hasSchemeClosedImmersionToSpec X ↔
      IsAffineFormalAlgebraicSpace X ∧
        ∃ (A : Type u) (_ : CommRing A) (structureHom : Spec (.of A) ⟶ S)
          (f : X ⟶ (full.bigTopology S).sheafifiedRepresentable (Over.mk structureHom)),
          ∀ (T : Over S)
            (t : (full.bigTopology S).sheafifiedRepresentable T ⟶ X),
            (MorphismProperty.inverseImage (@IsClosedImmersion) (full.bigToScheme S)).relative
                (full.bigTopology S).sheafifiedRepresentableFunctor t →
              (MorphismProperty.inverseImage (@IsClosedImmersion) (full.bigToScheme S)).relative
                (full.bigTopology S).sheafifiedRepresentableFunctor (t ≫ f))

/- Lemma 87.9.6: predicate specification. -/
#check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.hasAnySurjectiveLimitPresentation_iff X :
  hasAnySurjectiveLimitPresentation X ↔
      IsAffineFormalAlgebraicSpace X ∧
        ∀ (Λ : Type (u + 1)) [Preorder Λ] [IsDirected Λ (· ≤ ·)]
          (D : Λ ⥤ full.bigAffineSite S),
          IsDirectedAffineThickeningColimit D X → IsSurjectiveLimitGlobalSections D)

/- Lemma 87.9.6: the some-presentation condition is the canonical McQuillan property. -/
#check (AlgebraicGeometry.IsMcQuillan.iff X :
  IsMcQuillan X ↔
    IsAffineFormalAlgebraicSpace X ∧
      ∃ (Λ : Type (u + 1)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ full.bigAffineSite S),
        IsDirectedAffineThickeningColimit D X ∧ IsSurjectiveLimitGlobalSections D)
