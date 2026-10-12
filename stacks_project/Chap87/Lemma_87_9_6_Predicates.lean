/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import stacks_project.Chap87.Definition_87_9_9_Spf
public import stacks_project.Chap110.Lemma_110_75_1_McQuillan
public import stacks_project.Chap87.Lemma_87_9_6_OverScheme

/-!
# Characterizations of McQuillan affine formal algebraic spaces

Named predicates for the five equivalent conditions of Stacks tag 0AIC, on an
fppf sheaf on a chosen big site `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry.IsAffineFormalAlgebraicSpace

/-- `X` is the sheaf colimit of `Spec(A ⧸ I)` as `I` runs over all weak ideals of
definition of a weakly admissible topological ring `A` over `S`, realized on the
chosen site. -/
def isColimitOfWeakIdealSpectrum {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop :=
  ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
    (_ : TopologicalRing.IsWeaklyAdmissibleRing A)
    (structureHom : Spec (.of A) ⟶ 𝒮.toScheme.obj S)
    (D : WeakIdealOfDefinition A ⥤ 𝒮.bigAffineSite S)
    (e : ∀ I, (𝒮.bigAffineToScheme S).obj (D.obj I) ≅
      (stage A structureHom I).left),
    (∀ {I J : WeakIdealOfDefinition A} (f : I ⟶ J),
        (e I).hom ≫ ((thickenings A structureHom).map f).left =
          (𝒮.bigAffineToScheme S).map (D.map f) ≫ (e J).hom) ∧
      (∀ {I J : WeakIdealOfDefinition A} (f : I ⟶ J),
        IsThickening ((𝒮.bigAffineToScheme S).map (D.map f))) ∧
      ∃ (c : Cocone
          (D ⋙ 𝒮.bigAffineInclusion S ⋙
            (𝒮.bigTopology S).sheafifiedRepresentableFunctor)),
        Nonempty (IsColimit c) ∧ Nonempty (X ≅ c.pt)

/-- Unfold `isColimitOfWeakIdealSpectrum` as a weakly admissible ring over `S`
together with a chosen-site diagram isomorphic to the affine stages
`Spec(A ⧸ I)` whose sheaf colimit is `X`. -/
theorem isColimitOfWeakIdealSpectrum_iff {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    isColimitOfWeakIdealSpectrum X ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : TopologicalRing.IsWeaklyAdmissibleRing A)
        (structureHom : Spec (.of A) ⟶ 𝒮.toScheme.obj S)
        (D : WeakIdealOfDefinition A ⥤ 𝒮.bigAffineSite S)
        (e : ∀ I, (𝒮.bigAffineToScheme S).obj (D.obj I) ≅
          (stage A structureHom I).left),
        (∀ {I J : WeakIdealOfDefinition A} (f : I ⟶ J),
            (e I).hom ≫ ((thickenings A structureHom).map f).left =
              (𝒮.bigAffineToScheme S).map (D.map f) ≫ (e J).hom) ∧
          (∀ {I J : WeakIdealOfDefinition A} (f : I ⟶ J),
            IsThickening ((𝒮.bigAffineToScheme S).map (D.map f))) ∧
          ∃ (c : Cocone
              (D ⋙ 𝒮.bigAffineInclusion S ⋙
                (𝒮.bigTopology S).sheafifiedRepresentableFunctor)),
            Nonempty (IsColimit c) ∧ Nonempty (X ≅ c.pt) :=
  sorry

/-- `X` is an affine formal algebraic space admitting a map to `Spec(A)` over `S`
such that every closed immersion from an affine scheme remains a closed
immersion after composing to `Spec(A)`. -/
def hasAffineClosedImmersionToSpec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop :=
  IsAffineFormalAlgebraicSpace X ∧
    ∃ (A : Type u) (_ : CommRing A)
      (structureHom : Spec (.of A) ⟶ 𝒮.toScheme.obj S)
      (f : X ⟶ overSchemeSheaf (Spec (.of A)) structureHom),
      ∀ (T : 𝒮.bigAffineSite S)
        (t : (𝒮.bigTopology S).sheafifiedRepresentable
          ((𝒮.bigAffineInclusion S).obj T) ⟶ X),
        (MorphismProperty.inverseImage (@IsClosedImmersion) (𝒮.bigToScheme S)).relative
            (𝒮.bigTopology S).sheafifiedRepresentableFunctor t →
          IsClosedImmersion
            (overSchemeSheaf.homEquiv ((𝒮.bigAffineInclusion S).obj T) (t ≫ f)).val

/-- Unfold `hasAffineClosedImmersionToSpec` as an affine formal algebraic space
together with an `S`-algebra map to `Spec(A)` sending affine closed immersions
to closed immersions. -/
theorem hasAffineClosedImmersionToSpec_iff {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    hasAffineClosedImmersionToSpec X ↔
      IsAffineFormalAlgebraicSpace X ∧
        ∃ (A : Type u) (_ : CommRing A)
          (structureHom : Spec (.of A) ⟶ 𝒮.toScheme.obj S)
          (f : X ⟶ overSchemeSheaf (Spec (.of A)) structureHom),
          ∀ (T : 𝒮.bigAffineSite S)
            (t : (𝒮.bigTopology S).sheafifiedRepresentable
              ((𝒮.bigAffineInclusion S).obj T) ⟶ X),
            (MorphismProperty.inverseImage (@IsClosedImmersion)
                (𝒮.bigToScheme S)).relative
                (𝒮.bigTopology S).sheafifiedRepresentableFunctor t →
              IsClosedImmersion
                (overSchemeSheaf.homEquiv ((𝒮.bigAffineInclusion S).obj T)
                  (t ≫ f)).val :=
  sorry

/-- For an affine test object, the geometric closed-immersion condition on
`T ⟶ Spec(A)` is equivalent to surjectivity of the induced map on global
sections. -/
theorem isClosedImmersion_homEquiv_iff_surjective_on_Γ
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))] {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ 𝒮.toScheme.obj S)
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ overSchemeSheaf (Spec (.of A)) structureHom)
    (T : 𝒮.bigAffineSite S)
    (t : (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj T) ⟶ X) :
    IsClosedImmersion
        (overSchemeSheaf.homEquiv ((𝒮.bigAffineInclusion S).obj T) (t ≫ f)).val ↔
      Function.Surjective
        (overSchemeSheaf.homEquiv ((𝒮.bigAffineInclusion S).obj T) (t ≫ f)).val.appTop :=
  sorry

/-- `X` is an affine formal algebraic space admitting a map to `Spec(A)` over `S`
such that every closed immersion from a scheme remains a closed immersion after
composing to `Spec(A)`. -/
def hasSchemeClosedImmersionToSpec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop :=
  IsAffineFormalAlgebraicSpace X ∧
    ∃ (A : Type u) (_ : CommRing A)
      (structureHom : Spec (.of A) ⟶ 𝒮.toScheme.obj S)
      (f : X ⟶ overSchemeSheaf (Spec (.of A)) structureHom),
      ∀ (T : 𝒮.bigSite S)
        (t : (𝒮.bigTopology S).sheafifiedRepresentable T ⟶ X),
        (MorphismProperty.inverseImage (@IsClosedImmersion) (𝒮.bigToScheme S)).relative
            (𝒮.bigTopology S).sheafifiedRepresentableFunctor t →
          IsClosedImmersion (overSchemeSheaf.homEquiv T (t ≫ f)).val

/-- Unfold `hasSchemeClosedImmersionToSpec` as an affine formal algebraic space
together with an `S`-algebra map to `Spec(A)` sending closed immersions from
schemes to closed immersions. -/
theorem hasSchemeClosedImmersionToSpec_iff {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    hasSchemeClosedImmersionToSpec X ↔
      IsAffineFormalAlgebraicSpace X ∧
        ∃ (A : Type u) (_ : CommRing A)
          (structureHom : Spec (.of A) ⟶ 𝒮.toScheme.obj S)
          (f : X ⟶ overSchemeSheaf (Spec (.of A)) structureHom),
          ∀ (T : 𝒮.bigSite S)
            (t : (𝒮.bigTopology S).sheafifiedRepresentable T ⟶ X),
            (MorphismProperty.inverseImage (@IsClosedImmersion)
                (𝒮.bigToScheme S)).relative
                (𝒮.bigTopology S).sheafifiedRepresentableFunctor t →
              IsClosedImmersion (overSchemeSheaf.homEquiv T (t ≫ f)).val :=
  sorry

/-- `X` is an affine formal algebraic space and some directed affine thickening
presentation as in Definition 87.9.1 has surjective inverse-limit projections
on global sections. -/
def hasSomeSurjectiveLimitPresentation {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop :=
  IsAffineFormalAlgebraicSpace X ∧
    ∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ 𝒮.bigAffineSite S),
      IsDirectedAffineThickeningColimit D X ∧ IsSurjectiveLimitGlobalSections D

/-- Unfold `hasSomeSurjectiveLimitPresentation` as an affine formal algebraic
space together with one directed affine thickening presentation with surjective
inverse-limit projections on global sections. -/
theorem hasSomeSurjectiveLimitPresentation_iff {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    hasSomeSurjectiveLimitPresentation X ↔
      IsAffineFormalAlgebraicSpace X ∧
        ∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
          (D : Λ ⥤ 𝒮.bigAffineSite S),
          IsDirectedAffineThickeningColimit D X ∧
            IsSurjectiveLimitGlobalSections D :=
  sorry

/-- `X` is McQuillan if and only if it satisfies
`hasSomeSurjectiveLimitPresentation`. -/
theorem isMcQuillan_iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsMcQuillan X ↔ hasSomeSurjectiveLimitPresentation X :=
  sorry

/-- `X` is an affine formal algebraic space and every directed affine thickening
presentation as in Definition 87.9.1 has surjective inverse-limit projections
on global sections. -/
def hasAnySurjectiveLimitPresentation {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop :=
  IsAffineFormalAlgebraicSpace X ∧
    ∀ (Λ : Type (max u v)) [Preorder Λ] [IsDirected Λ (· ≤ ·)]
      (D : Λ ⥤ 𝒮.bigAffineSite S),
      IsDirectedAffineThickeningColimit D X → IsSurjectiveLimitGlobalSections D

/-- Unfold `hasAnySurjectiveLimitPresentation` as an affine formal algebraic
space whose every directed affine thickening presentation has surjective
inverse-limit projections on global sections. -/
theorem hasAnySurjectiveLimitPresentation_iff {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    hasAnySurjectiveLimitPresentation X ↔
      IsAffineFormalAlgebraicSpace X ∧
        ∀ (Λ : Type (max u v)) [Preorder Λ] [IsDirected Λ (· ≤ ·)]
          (D : Λ ⥤ 𝒮.bigAffineSite S),
          IsDirectedAffineThickeningColimit D X →
            IsSurjectiveLimitGlobalSections D :=
  sorry

/-- Condition (1) is equivalent to the affine closed-immersion condition (2). -/
theorem isColimitOfWeakIdealSpectrum_iff_hasAffineClosedImmersionToSpec
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsCoequalizerOfRepresentables X] :
    isColimitOfWeakIdealSpectrum X ↔ hasAffineClosedImmersionToSpec X :=
  sorry

/-- Condition (2) is equivalent to the scheme closed-immersion condition (3). -/
theorem hasAffineClosedImmersionToSpec_iff_hasSchemeClosedImmersionToSpec
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsCoequalizerOfRepresentables X] :
    hasAffineClosedImmersionToSpec X ↔ hasSchemeClosedImmersionToSpec X :=
  sorry

/-- Condition (3) is equivalent to existence of some surjective-limit
presentation (4). -/
theorem hasSchemeClosedImmersionToSpec_iff_hasSomeSurjectiveLimitPresentation
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsCoequalizerOfRepresentables X] :
    hasSchemeClosedImmersionToSpec X ↔ hasSomeSurjectiveLimitPresentation X :=
  sorry

/-- Condition (4) is equivalent to the any-presentation condition (5). -/
theorem hasSomeSurjectiveLimitPresentation_iff_hasAnySurjectiveLimitPresentation
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsCoequalizerOfRepresentables X] :
    hasSomeSurjectiveLimitPresentation X ↔ hasAnySurjectiveLimitPresentation X :=
  sorry

end AlgebraicGeometry.IsAffineFormalAlgebraicSpace
