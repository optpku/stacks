/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.McQuillan.Reconstruction

/-!
# Weak ideals and representable thickenings
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

/-- A morphism into an affine thickening colimit is the quotient by an ideal of the inverse-limit ring when it factors over the base through a stage by the canonical quotient-spectrum immersion. -/
def IsWeakIdealQuotient
    {X : Sheaf (full.bigTopology S) (Type (u + 1))}
    {Λ : Type (u + 1)} [Preorder Λ]
    (D : Λ ⥤ full.bigAffineSite S)
    (c : Cocone (D ⋙ full.bigAffineInclusion S ⋙
      (full.bigTopology S).sheafifiedRepresentableFunctor))
    (hX : X ≅ c.pt) (I : Ideal (limitGlobalSections D))
    (T : Over S) (t : (full.bigTopology S).sheafifiedRepresentable T ⟶ X) : Prop :=
  ∃ (i : Λ), RingHom.ker (limitGlobalSections.eval D i) ≤ I ∧
    ∃ (g : T ⟶ (full.bigAffineInclusion S).obj (D.obj i))
      (e : T.left ≅ Spec (.of
        (Γ((full.bigAffineToScheme S).obj (D.obj i), ⊤) ⧸
          Ideal.map (limitGlobalSections.eval D i) I))),
      g.left = e.hom ≫
        Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.map (limitGlobalSections.eval D i) I))) ≫
        (@Scheme.isoSpec ((full.bigAffineToScheme S).obj (D.obj i))
          (D.obj i).property).inv ∧
      (full.bigTopology S).sheafifiedRepresentableFunctor.map g ≫
        c.ι.app i ≫ hX.inv = t

/-- Weak ideals of a realizing ring classify representable thickenings into its formal spectrum uniquely, by quotient-stage isomorphisms over the base commuting with the given morphism. -/
theorem classifiesRepresentableThickenings_of_weakIdealSpectrum
    {X : Sheaf (full.bigTopology S) (Type (u + 1))}
    [IsCoequalizerOfRepresentables X]
    (B : Type u) [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsWeaklyAdmissibleRing B]
    (structureHom : Spec (.of B) ⟶ S)
    (realization : X ≅ FppfFormalSpectrum.spf B structureHom)
    (T : Over S) (t : (full.bigTopology S).sheafifiedRepresentable T ⟶ X) :
    FppfFormalSpectrum.thickening S t ↔
      ∃! I : WeakIdealOfDefinition B,
        ∃ e : T ≅ stage B structureHom I,
          (full.bigTopology S).sheafifiedRepresentableFunctor.map e.hom ≫
            FppfFormalSpectrum.spfι B structureHom (ULift.up I) ≫
              realization.inv = t :=
  sorry

/-- Every weak ideal of the inverse-limit ring is realized by a representable thickening into the affine thickening colimit. -/
theorem weakIdeal_quotient_exists
    {X : Sheaf (full.bigTopology S) (Type (u + 1))}
    [IsCoequalizerOfRepresentables X]
    {Λ : Type (u + 1)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ full.bigAffineSite S)
    (hD : IsDirectedAffineThickeningColimit D X)
    (hlim : IsSurjectiveLimitGlobalSections D)
    (c : Cocone (D ⋙ full.bigAffineInclusion S ⋙
      (full.bigTopology S).sheafifiedRepresentableFunctor))
    (hc : IsColimit c) (hX : X ≅ c.pt)
    (I : Ideal (limitGlobalSections D))
    (hI : @TopologicalRing.Ideal.IsWeakIdealOfDefinition (limitGlobalSections D)
      (instCommRingLimitGlobalSections D) (limitGlobalSectionsTopology D) I) :
    ∃ (T : Over S) (t : (full.bigTopology S).sheafifiedRepresentable T ⟶ X),
      FppfFormalSpectrum.thickening S t ∧ IsWeakIdealQuotient D c hX I T t :=
  sorry

/-- Representable thickenings into an affine thickening colimit correspond to unique weak ideals of its inverse-limit ring through the canonical quotient morphisms. -/
theorem classifiesRepresentableThickenings
    {X : Sheaf (full.bigTopology S) (Type (u + 1))}
    [IsCoequalizerOfRepresentables X]
    {Λ : Type (u + 1)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ full.bigAffineSite S)
    (hD : IsDirectedAffineThickeningColimit D X)
    (hlim : IsSurjectiveLimitGlobalSections D)
    (c : Cocone (D ⋙ full.bigAffineInclusion S ⋙
      (full.bigTopology S).sheafifiedRepresentableFunctor))
    (hc : IsColimit c) (hX : X ≅ c.pt)
    (T : Over S) (t : (full.bigTopology S).sheafifiedRepresentable T ⟶ X) :
    FppfFormalSpectrum.thickening S t ↔
      ∃! I : Ideal (limitGlobalSections D),
        @TopologicalRing.Ideal.IsWeakIdealOfDefinition (limitGlobalSections D)
          (instCommRingLimitGlobalSections D) (limitGlobalSectionsTopology D) I ∧
            IsWeakIdealQuotient D c hX I T t :=
  sorry

end AlgebraicGeometry.IsAffineFormalAlgebraicSpace
