module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.McQuillan.Reconstruction

/-!
# Criteria for weakly admissible affine formal spectra
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.IsAffineFormalAlgebraicSpace

variable {S : Scheme.{u}}
  [HasWeakSheafify (full.bigTopology S) (Type (u + 1))]
  [HasPullbacks (Sheaf (full.bigTopology S) (Type (u + 1)))]

/-- A sheaf is a weakly admissible affine formal spectrum when it is isomorphic over the base to the colimit of all weak-ideal quotient spectra of a weakly admissible ring. -/
def isColimitOfWeakIdealSpectrum
    (X : Sheaf (full.bigTopology S) (Type (u + 1))) : Prop :=
  ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
    (_ : TopologicalRing.IsWeaklyAdmissibleRing A)
    (structureHom : Spec (.of A) ⟶ S),
    Nonempty (X ≅ FppfFormalSpectrum.spf A structureHom)

/-- Being a weakly admissible affine formal spectrum is equivalent to existence of a realizing ring over the base. -/
theorem isColimitOfWeakIdealSpectrum_iff
    (X : Sheaf (full.bigTopology S) (Type (u + 1))) :
    isColimitOfWeakIdealSpectrum X ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : TopologicalRing.IsWeaklyAdmissibleRing A)
        (structureHom : Spec (.of A) ⟶ S),
        Nonempty (X ≅ FppfFormalSpectrum.spf A structureHom) :=
  Iff.rfl

/-- An affine formal algebraic space has an affine target preserving closed immersions from every affine test scheme. -/
def hasAffineClosedImmersionToSpec
    (X : Sheaf (full.bigTopology S) (Type (u + 1))) : Prop :=
  IsAffineFormalAlgebraicSpace X ∧
    ∃ (A : Type u) (_ : CommRing A) (structureHom : Spec (.of A) ⟶ S)
      (f : X ⟶ (full.bigTopology S).sheafifiedRepresentable (Over.mk structureHom)),
      ∀ (T : full.bigAffineSite S)
        (t : (full.bigTopology S).sheafifiedRepresentable
          ((full.bigAffineInclusion S).obj T) ⟶ X),
        (MorphismProperty.inverseImage (@IsClosedImmersion) (full.bigToScheme S)).relative
            (full.bigTopology S).sheafifiedRepresentableFunctor t →
          (MorphismProperty.inverseImage (@IsClosedImmersion) (full.bigToScheme S)).relative
            (full.bigTopology S).sheafifiedRepresentableFunctor (t ≫ f)

/-- The affine-test condition consists of an affine formal algebraic space and a map to an affine spectrum preserving closed immersions from affine schemes. -/
theorem hasAffineClosedImmersionToSpec_iff
    (X : Sheaf (full.bigTopology S) (Type (u + 1))) :
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
                (full.bigTopology S).sheafifiedRepresentableFunctor (t ≫ f) :=
  Iff.rfl

/-- An affine formal algebraic space has an affine target preserving closed immersions from every scheme over the base. -/
def hasSchemeClosedImmersionToSpec
    (X : Sheaf (full.bigTopology S) (Type (u + 1))) : Prop :=
  IsAffineFormalAlgebraicSpace X ∧
    ∃ (A : Type u) (_ : CommRing A) (structureHom : Spec (.of A) ⟶ S)
      (f : X ⟶ (full.bigTopology S).sheafifiedRepresentable (Over.mk structureHom)),
      ∀ (T : Over S)
        (t : (full.bigTopology S).sheafifiedRepresentable T ⟶ X),
        (MorphismProperty.inverseImage (@IsClosedImmersion) (full.bigToScheme S)).relative
            (full.bigTopology S).sheafifiedRepresentableFunctor t →
          (MorphismProperty.inverseImage (@IsClosedImmersion) (full.bigToScheme S)).relative
            (full.bigTopology S).sheafifiedRepresentableFunctor (t ≫ f)

/-- The scheme-test condition consists of an affine formal algebraic space and a map to an affine spectrum preserving closed immersions from arbitrary schemes. -/
theorem hasSchemeClosedImmersionToSpec_iff
    (X : Sheaf (full.bigTopology S) (Type (u + 1))) :
    hasSchemeClosedImmersionToSpec X ↔
      IsAffineFormalAlgebraicSpace X ∧
        ∃ (A : Type u) (_ : CommRing A) (structureHom : Spec (.of A) ⟶ S)
          (f : X ⟶ (full.bigTopology S).sheafifiedRepresentable (Over.mk structureHom)),
          ∀ (T : Over S)
            (t : (full.bigTopology S).sheafifiedRepresentable T ⟶ X),
            (MorphismProperty.inverseImage (@IsClosedImmersion) (full.bigToScheme S)).relative
                (full.bigTopology S).sheafifiedRepresentableFunctor t →
              (MorphismProperty.inverseImage (@IsClosedImmersion) (full.bigToScheme S)).relative
                (full.bigTopology S).sheafifiedRepresentableFunctor (t ≫ f) :=
  Iff.rfl

/-- Every directed affine thickening presentation of an affine formal algebraic space has surjective projections on inverse-limit sections. -/
def hasAnySurjectiveLimitPresentation
    (X : Sheaf (full.bigTopology S) (Type (u + 1))) : Prop :=
  IsAffineFormalAlgebraicSpace X ∧
    ∀ (Λ : Type (u + 1)) [Preorder Λ] [IsDirected Λ (· ≤ ·)]
      (D : Λ ⥤ full.bigAffineSite S),
      IsDirectedAffineThickeningColimit D X → IsSurjectiveLimitGlobalSections D

/-- The universal surjectivity condition quantifies over all directed affine thickening presentations. -/
theorem hasAnySurjectiveLimitPresentation_iff
    (X : Sheaf (full.bigTopology S) (Type (u + 1))) :
    hasAnySurjectiveLimitPresentation X ↔
      IsAffineFormalAlgebraicSpace X ∧
        ∀ (Λ : Type (u + 1)) [Preorder Λ] [IsDirected Λ (· ≤ ·)]
          (D : Λ ⥤ full.bigAffineSite S),
          IsDirectedAffineThickeningColimit D X → IsSurjectiveLimitGlobalSections D :=
  Iff.rfl

/-- A weakly admissible formal-spectrum realization is equivalent to the affine-test closed-immersion condition. -/
theorem isColimitOfWeakIdealSpectrum_iff_hasAffineClosedImmersionToSpec
    (X : Sheaf (full.bigTopology S) (Type (u + 1)))
    [IsCoequalizerOfRepresentables X] :
    isColimitOfWeakIdealSpectrum X ↔ hasAffineClosedImmersionToSpec X :=
  sorry

/-- Preserving affine-test closed immersions is equivalent to preserving closed immersions from all schemes. -/
theorem hasAffineClosedImmersionToSpec_iff_hasSchemeClosedImmersionToSpec
    (X : Sheaf (full.bigTopology S) (Type (u + 1)))
    [IsCoequalizerOfRepresentables X] :
    hasAffineClosedImmersionToSpec X ↔ hasSchemeClosedImmersionToSpec X :=
  sorry

/-- The scheme-test closed-immersion condition is equivalent to the McQuillan property. -/
theorem hasSchemeClosedImmersionToSpec_iff_isMcQuillan
    (X : Sheaf (full.bigTopology S) (Type (u + 1)))
    [IsCoequalizerOfRepresentables X] :
    hasSchemeClosedImmersionToSpec X ↔ IsMcQuillan X :=
  sorry

/-- The McQuillan property is equivalent to surjectivity for every directed affine thickening presentation. -/
theorem isMcQuillan_iff_hasAnySurjectiveLimitPresentation
    (X : Sheaf (full.bigTopology S) (Type (u + 1)))
    [IsCoequalizerOfRepresentables X] :
    IsMcQuillan X ↔ hasAnySurjectiveLimitPresentation X :=
  sorry

/-- Formal-spectrum realization, the two closed-immersion criteria, and surjectivity for some or every directed affine thickening presentation are equivalent. -/
theorem tfae_mcquillan
    (X : Sheaf (full.bigTopology S) (Type (u + 1)))
    [IsCoequalizerOfRepresentables X] :
    List.TFAE [isColimitOfWeakIdealSpectrum X, hasAffineClosedImmersionToSpec X,
      hasSchemeClosedImmersionToSpec X, IsMcQuillan X,
      hasAnySurjectiveLimitPresentation X] :=
  sorry

end AlgebraicGeometry.IsAffineFormalAlgebraicSpace
