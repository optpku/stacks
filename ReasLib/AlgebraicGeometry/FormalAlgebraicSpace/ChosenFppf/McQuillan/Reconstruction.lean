/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.McQuillan
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.GlobalSections
public import ReasLib.AlgebraicGeometry.FormalSpectrum.ChosenFppf
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Reconstruction from inverse limits of affine sections
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- Surjectivity of compatible-family projections is surjectivity of each evaluation homomorphism. -/
theorem surjective_eval_limitGlobalSections {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} {Λ : Type (max u v)} [Preorder Λ]
    (D : Λ ⥤ 𝒮.bigAffineSite S) (hlim : IsSurjectiveLimitGlobalSections D)
    (i : Λ) : Function.Surjective (limitGlobalSections.eval D i) := by
  intro x
  obtain ⟨s, hs, hx⟩ := hlim i x
  exact ⟨⟨s, hs⟩, hx⟩

namespace IsAffineFormalAlgebraicSpace

/-- Kernels of projections in a surjective directed affine thickening presentation are weak ideals of definition for the inverse-limit topology. -/
theorem isWeakIdealOfDefinition_ker_eval {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))} {Λ : Type (max u v)}
    [Preorder Λ] [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ 𝒮.bigAffineSite S)
    (hD : IsDirectedAffineThickeningColimit D X)
    (hlim : IsSurjectiveLimitGlobalSections D) (i : Λ) :
    @TopologicalRing.Ideal.IsWeakIdealOfDefinition (limitGlobalSections D)
      (instCommRingLimitGlobalSections D) (limitGlobalSectionsTopology D)
      (RingHom.ker (limitGlobalSections.eval D i)) :=
  sorry

/-- The inverse limit of a surjective directed affine thickening presentation is weakly admissible with its limit topology. -/
theorem limitRing_isWeaklyAdmissible {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsCoequalizerOfRepresentables X] {Λ : Type (max u v)} [Preorder Λ]
    [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ 𝒮.bigAffineSite S)
    (hD : IsDirectedAffineThickeningColimit D X)
    (hlim : IsSurjectiveLimitGlobalSections D) :
    @TopologicalRing.IsWeaklyAdmissibleRing (limitGlobalSections D)
      (instCommRingLimitGlobalSections D) (limitGlobalSectionsTopology D) :=
  sorry

/-- A directed affine thickening presentation of a sheaf with a fixed-site representable presentation has a universe-small ring of compatible sections. -/
theorem small_limitGlobalSections {S : Scheme.{u}}
    [HasWeakSheafify (full.bigTopology S) (Type (u + 1))]
    [HasPullbacks (Sheaf (full.bigTopology S) (Type (u + 1)))]
    {X : Sheaf (full.bigTopology S) (Type (u + 1))}
    [IsCoequalizerOfRepresentables X] {Λ : Type (u + 1)} [Preorder Λ]
    [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ full.bigAffineSite S)
    (hD : IsDirectedAffineThickeningColimit D X) :
    Small.{u} (limitGlobalSections D) :=
  sorry

/-- A surjective directed affine thickening presentation is realized by a small weakly admissible ring topologically isomorphic to its ring of compatible sections. -/
theorem limitRing_presents {S : Scheme.{u}}
    [HasWeakSheafify (full.bigTopology S) (Type (u + 1))]
    [HasPullbacks (Sheaf (full.bigTopology S) (Type (u + 1)))]
    {X : Sheaf (full.bigTopology S) (Type (u + 1))}
    [IsCoequalizerOfRepresentables X] {Λ : Type (u + 1)} [Preorder Λ]
    [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ full.bigAffineSite S)
    (hD : IsDirectedAffineThickeningColimit D X)
    (hlim : IsSurjectiveLimitGlobalSections D) :
    ∃ (B : Type u) (_ : CommRing B) (_ : TopologicalSpace B)
      (_ : TopologicalRing.IsWeaklyAdmissibleRing B)
      (structureHom : Spec (.of B) ⟶ S) (e : B ≃+* limitGlobalSections D),
      @Continuous B (limitGlobalSections D) _ (limitGlobalSectionsTopology D) e ∧
        @Continuous (limitGlobalSections D) B (limitGlobalSectionsTopology D) _ e.symm ∧
          Nonempty (X ≅ FppfFormalSpectrum.spf B structureHom) :=
  sorry

/-- A ring realizing a formal spectrum is canonically topologically identified with the inverse limit of every directed affine thickening presentation: evaluation agrees with every quotient-stage factorization. -/
theorem weakIdealSpectrum_limit_identification {S : Scheme.{u}}
    [HasWeakSheafify (full.bigTopology S) (Type (u + 1))]
    [HasPullbacks (Sheaf (full.bigTopology S) (Type (u + 1)))]
    {X : Sheaf (full.bigTopology S) (Type (u + 1))}
    [IsCoequalizerOfRepresentables X]
    (B : Type u) [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsWeaklyAdmissibleRing B]
    (structureHom : Spec (.of B) ⟶ S)
    (realization : X ≅ FppfFormalSpectrum.spf B structureHom)
    {Λ : Type (u + 1)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ full.bigAffineSite S)
    (hD : IsDirectedAffineThickeningColimit D X)
    (c : Cocone (D ⋙ full.bigAffineInclusion S ⋙
      (full.bigTopology S).sheafifiedRepresentableFunctor))
    (hc : IsColimit c) (hX : X ≅ c.pt) :
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
                    (Ideal.Quotient.mk I.ideal)) :=
  sorry

end IsAffineFormalAlgebraicSpace
end AlgebraicGeometry
