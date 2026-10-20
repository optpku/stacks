/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.McQuillan.Criteria
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.McQuillan.Classification
import StacksCheckRecall

/-!
# Lemma 87.9.6

The five McQuillan criteria, inverse-limit reconstruction, and classification
of representable thickenings by weak ideals of definition.
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
  [IsCoequalizerOfRepresentables X]

/- Lemma 87.9.6: the five equivalent conditions, with the fixed-site size hypothesis. -/
@[stacks 0AIC] #check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.tfae_mcquillan X :
  List.TFAE [isColimitOfWeakIdealSpectrum X, hasAffineClosedImmersionToSpec X,
      hasSchemeClosedImmersionToSpec X, IsMcQuillan X,
      hasAnySurjectiveLimitPresentation X])

variable {Λ : Type (u + 1)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
  (D : Λ ⥤ full.bigAffineSite S)
  (hD : IsDirectedAffineThickeningColimit D X)
  (hlim : IsSurjectiveLimitGlobalSections D)

/- Lemma 87.9.6 (moreover): the actual inverse-limit ring is weakly admissible. -/
@[stacks 0AIC] #check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.limitRing_isWeaklyAdmissible D hD hlim :
  @TopologicalRing.IsWeaklyAdmissibleRing (limitGlobalSections D)
      (instCommRingLimitGlobalSections D) (limitGlobalSectionsTopology D))

/- Lemma 87.9.6 (moreover): a small topological model of the limit ring realizes X. -/
@[stacks 0AIC] #check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.limitRing_presents D hD hlim :
  ∃ (B : Type u) (_ : CommRing B) (_ : TopologicalSpace B)
      (_ : TopologicalRing.IsWeaklyAdmissibleRing B)
      (structureHom : Spec (.of B) ⟶ S) (e : B ≃+* limitGlobalSections D),
      @Continuous B (limitGlobalSections D) _ (limitGlobalSectionsTopology D) e ∧
        @Continuous (limitGlobalSections D) B (limitGlobalSectionsTopology D) _ e.symm ∧
          Nonempty (X ≅ FppfFormalSpectrum.spf B structureHom))

variable (c : Cocone (D ⋙ full.bigAffineInclusion S ⋙
    (full.bigTopology S).sheafifiedRepresentableFunctor))
  (hc : IsColimit c) (hX : X ≅ c.pt)
  (B : Type u) [CommRing B] [TopologicalSpace B]
  [TopologicalRing.IsWeaklyAdmissibleRing B]
  (structureHom : Spec (.of B) ⟶ S)
  (realization : X ≅ FppfFormalSpectrum.spf B structureHom)

/- Lemma 87.9.6 (moreover): every realizing ring is canonically the topological inverse limit. -/
@[stacks 0AIC] #check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.weakIdealSpectrum_limit_identification B structureHom realization D hD c hc hX :
  IsSurjectiveLimitGlobalSections D ∧
      ∃ e : B ≃+* limitGlobalSections D,
        @Continuous B (limitGlobalSections D) _ (limitGlobalSectionsTopology D) e ∧
          @Continuous (limitGlobalSections D) B (limitGlobalSectionsTopology D) _ e.symm ∧
            ∀ (i : Λ) (I : WeakIdealOfDefinition B)
              (g : (full.bigAffineInclusion S).obj (D.obj i) ⟶ stage B structureHom I),
              (full.bigTopology S).sheafifiedRepresentableFunctor.map g ≫
                  FppfFormalSpectrum.spfι B structureHom (ULift.up I) =
                c.ι.app i ≫ hX.inv ≫ realization.hom →
              (limitGlobalSections.eval D i).comp e.toRingHom =
                g.left.appTop.hom.comp
                  ((Scheme.ΓSpecIso (.of (B ⧸ I.ideal))).inv.hom.comp
                    (Ideal.Quotient.mk I.ideal)))

variable (T : Over S)
  (t : (full.bigTopology S).sheafifiedRepresentable T ⟶ X)

/- Lemma 87.9.6 (moreover): representable thickenings correspond to unique weak ideals. -/
@[stacks 0AIC] #check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.classifiesRepresentableThickenings D hD hlim c hc hX T t :
  FppfFormalSpectrum.thickening S t ↔
      ∃! I : Ideal (limitGlobalSections D),
        @TopologicalRing.Ideal.IsWeakIdealOfDefinition (limitGlobalSections D)
          (instCommRingLimitGlobalSections D) (limitGlobalSectionsTopology D) I ∧
            IsWeakIdealQuotient D c hX I T t)

variable (I : Ideal (limitGlobalSections D))
  (hI : @TopologicalRing.Ideal.IsWeakIdealOfDefinition (limitGlobalSections D)
    (instCommRingLimitGlobalSections D) (limitGlobalSectionsTopology D) I)

/- Lemma 87.9.6 (moreover): every weak ideal is realized by a representable thickening. -/
@[stacks 0AIC] #check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.weakIdeal_quotient_exists D hD hlim c hc hX I hI :
  ∃ (T : Over S) (t : (full.bigTopology S).sheafifiedRepresentable T ⟶ X),
      FppfFormalSpectrum.thickening S t ∧ IsWeakIdealQuotient D c hX I T t)

