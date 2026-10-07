module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Defs.Induced
public import stacks_project.Chap87.Remark_87_35_2
public import stacks_project.Chap87.Lemma_87_9_6_OverScheme
public import stacks_project.Chap87.Lemma_87_9_6_Predicates

/-!
# Lemma 87.9.6

Characterizations of affine formal algebraic spaces that are `Spf` of a weakly
admissible topological ring, on an fppf sheaf satisfying the coequalizer size
condition of Remark 87.11.5.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.ChosenBigFppfSite AlgebraicGeometry.IsAffineFormalAlgebraicSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.IsAffineFormalAlgebraicSpace

/-- Lemma 87.9.6 (1): Let `S` be a scheme. Let `X` be an fppf sheaf on
`(Sch/S)_fppf` which satisfies the set theoretic condition of Remark 87.11.5.
The following are equivalent: there exists a weakly admissible topological ring
`A` over `S` such that `X` is the sheaf colimit of `Spec(A ⧸ I)` over weak
ideals of definition; `X` is an affine formal algebraic space and there exists
an `S`-algebra `A` and a map `X ⟶ Spec(A)` such that for a closed immersion
`T ⟶ X` with `T` an affine scheme the composition `T ⟶ Spec(A)` is a closed
immersion; the same with `T` any scheme; `X` is an affine formal algebraic space
and for some presentation `X ≅ colim X_λ` as in Definition 87.9.1 the
projections `lim Γ(X_λ, ⊤) ⟶ Γ(X_λ, ⊤)` are surjective; the same for any such
presentation. -/
@[stacks 0AIC]
theorem tfae_mcquillan {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsCoequalizerOfRepresentables X] :
    List.TFAE [isColimitOfWeakIdealSpectrum X, hasAffineClosedImmersionToSpec X,
      hasSchemeClosedImmersionToSpec X, hasSomeSurjectiveLimitPresentation X,
      hasAnySurjectiveLimitPresentation X] :=
  sorry

/-- Inverse-limit topology on compatible families of global sections, initial
with respect to the discrete topologies on the stage rings `Γ(X_i, ⊤)`. -/
@[reducible] def limitGlobalSectionsTopology {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} {Λ : Type (max u v)} [Preorder Λ]
    (D : Λ ⥤ 𝒮.bigAffineSite S) :
    TopologicalSpace (limitGlobalSections D) :=
  ⨅ i : Λ,
    TopologicalSpace.induced (fun s : limitGlobalSections D ↦ s.val i)
      (⊥ : TopologicalSpace
        (Γ((𝒮.bigAffineToScheme S).obj (D.obj i), ⊤) : Type u))

/-- `limitGlobalSectionsTopology` is the infimum of the topologies induced by
the discrete topologies along the projections. -/
theorem limitGlobalSectionsTopology_def {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} {Λ : Type (max u v)} [Preorder Λ]
    (D : Λ ⥤ 𝒮.bigAffineSite S) :
    limitGlobalSectionsTopology D =
      ⨅ i : Λ,
        TopologicalSpace.induced (fun s : limitGlobalSections D ↦ s.val i)
          (⊥ : TopologicalSpace
            (Γ((𝒮.bigAffineToScheme S).obj (D.obj i), ⊤) : Type u)) :=
  sorry

/-- Projection from inverse-limit global sections onto a stage ring. -/
def limitGlobalSections.eval {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    {Λ : Type (max u v)} [Preorder Λ] (D : Λ ⥤ 𝒮.bigAffineSite S) (i : Λ) :
    limitGlobalSections D →+*
      (Γ((𝒮.bigAffineToScheme S).obj (D.obj i), ⊤) : Type u) where
  toFun s := s.val i
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- `limitGlobalSections.eval D i` evaluates a compatible family at stage `i`. -/
theorem limitGlobalSections.eval_apply {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} {Λ : Type (max u v)} [Preorder Λ]
    (D : Λ ⥤ 𝒮.bigAffineSite S) (i : Λ) (s : limitGlobalSections D) :
    limitGlobalSections.eval D i s = s.val i :=
  sorry

/-- Each projection is continuous for the limit topology and the discrete
topology on the stage ring. -/
theorem continuous_eval_limitGlobalSections {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} {Λ : Type (max u v)} [Preorder Λ]
    (D : Λ ⥤ 𝒮.bigAffineSite S) (i : Λ) :
    @Continuous (limitGlobalSections D)
      (Γ((𝒮.bigAffineToScheme S).obj (D.obj i), ⊤) : Type u)
      (limitGlobalSectionsTopology D) ⊥ (limitGlobalSections.eval D i) :=
  sorry

/-- In a directed affine thickening presentation with surjective inverse-limit
projections, the kernel of a stage projection is a weak ideal of definition
for the limit topology. -/
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

/-- In a surjective-limit presentation the stage projections are surjective. -/
theorem surjective_eval_limitGlobalSections {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} {Λ : Type (max u v)} [Preorder Λ]
    (D : Λ ⥤ 𝒮.bigAffineSite S) (hlim : IsSurjectiveLimitGlobalSections D)
    (i : Λ) : Function.Surjective (limitGlobalSections.eval D i) :=
  sorry

/-- The kernel of a stage projection presents that stage ring: the quotient of
`limitGlobalSections D` by the kernel is isomorphic to `Γ(X_i, ⊤)`, without
identifying the `Type (max u v)` limit ring with a `Type u` model. -/
theorem quotientKer_eval_equiv_stage {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} {Λ : Type (max u v)} [Preorder Λ]
    (D : Λ ⥤ 𝒮.bigAffineSite S) (hlim : IsSurjectiveLimitGlobalSections D)
    (i : Λ) :
    Nonempty
      ((limitGlobalSections D ⧸ RingHom.ker (limitGlobalSections.eval D i)) ≃+*
        (Γ((𝒮.bigAffineToScheme S).obj (D.obj i), ⊤) : Type u)) :=
  sorry

/-- Lemma 87.9.6 (2): in a directed affine thickening presentation with
surjective inverse-limit projections, as in the equivalent conditions above,
the weakly admissible topological ring is `A = lim Γ(X_λ, ⊤)` endowed with
`limitGlobalSectionsTopology`. -/
@[stacks 0AIC]
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

/-- Lemma 87.9.6 (3): in the directed affine thickening presentation of
`limitRing_isWeaklyAdmissible`, the weak ideals of definition of
`lim Γ(X_λ, ⊤)` with the limit topology classify exactly the morphisms
`T ⟶ X` which are representable and thickenings. Such a morphism corresponds
to some weak ideal `I` containing the kernel of a stage projection, with
`T ≅ Spec(Γ(X_i, ⊤) ⧸ I Γ(X_i, ⊤))`, and `t` the resulting thickening into
that stage followed by the cocone leg. -/
@[stacks 0AIC]
theorem classifiesRepresentableThickenings {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsCoequalizerOfRepresentables X] {Λ : Type (max u v)} [Preorder Λ]
    [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ 𝒮.bigAffineSite S)
    (hD : IsDirectedAffineThickeningColimit D X)
    (hlim : IsSurjectiveLimitGlobalSections D)
    (c : Cocone
      (D ⋙ 𝒮.bigAffineInclusion S ⋙
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
    (hc : IsColimit c) (hX : X ≅ c.pt) (T : 𝒮.bigSite S)
    (t : (𝒮.bigTopology S).sheafifiedRepresentable T ⟶ X) :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable t ∧
        (MorphismProperty.inverseImage (@IsThickening) (𝒮.bigToScheme S)).relative
          (𝒮.bigTopology S).sheafifiedRepresentableFunctor t ↔
      ∃ (I : Ideal (limitGlobalSections D)),
        @TopologicalRing.Ideal.IsWeakIdealOfDefinition (limitGlobalSections D)
            (instCommRingLimitGlobalSections D) (limitGlobalSectionsTopology D) I ∧
          ∃ (i : Λ), RingHom.ker (limitGlobalSections.eval D i) ≤ I ∧
            Nonempty
                ((𝒮.bigToScheme S).obj T ≅
                  Spec (.of
                    (Γ((𝒮.bigAffineToScheme S).obj (D.obj i), ⊤) ⧸
                      Ideal.map (limitGlobalSections.eval D i) I))) ∧
              ∃ (g : (𝒮.bigTopology S).sheafifiedRepresentable T ⟶
                  (𝒮.bigTopology S).sheafifiedRepresentable
                    ((𝒮.bigAffineInclusion S).obj (D.obj i))),
                (MorphismProperty.inverseImage (@IsThickening)
                    (𝒮.bigToScheme S)).relative
                    (𝒮.bigTopology S).sheafifiedRepresentableFunctor g ∧
                  g ≫ c.ι.app i ≫ hX.inv = t :=
  sorry

/-- For a weakly admissible ring realizing `X` as the sheaf colimit of
`Spec(A ⧸ I)` over all weak ideals of definition, those ideals classify
representable thickenings `T ⟶ X` by identifying `T` with the corresponding
stage. -/
theorem classifiesRepresentableThickenings_of_weakIdealSpectrum
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsCoequalizerOfRepresentables X] {A : Type u} [CommRing A]
    [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    (structureHom : Spec (.of A) ⟶ 𝒮.toScheme.obj S)
    (D : WeakIdealOfDefinition A ⥤ 𝒮.bigAffineSite S)
    (e : ∀ I, (𝒮.bigAffineToScheme S).obj (D.obj I) ≅
      (stage A structureHom I).left)
    (he : ∀ {I J : WeakIdealOfDefinition A} (f : I ⟶ J),
      (e I).hom ≫ ((thickenings A structureHom).map f).left =
        (𝒮.bigAffineToScheme S).map (D.map f) ≫ (e J).hom)
    (hthick : ∀ {I J : WeakIdealOfDefinition A} (f : I ⟶ J),
      IsThickening ((𝒮.bigAffineToScheme S).map (D.map f)))
    (c : Cocone
      (D ⋙ 𝒮.bigAffineInclusion S ⋙
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
    (hc : IsColimit c) (hX : X ≅ c.pt) (T : 𝒮.bigSite S)
    (t : (𝒮.bigTopology S).sheafifiedRepresentable T ⟶ X) :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable t ∧
        (MorphismProperty.inverseImage (@IsThickening) (𝒮.bigToScheme S)).relative
          (𝒮.bigTopology S).sheafifiedRepresentableFunctor t ↔
      ∃ (I : WeakIdealOfDefinition A),
        Nonempty ((𝒮.bigToScheme S).obj T ≅ Spec (.of (A ⧸ I.ideal))) ∧
          ∃ (g : (𝒮.bigTopology S).sheafifiedRepresentable T ⟶
              (𝒮.bigTopology S).sheafifiedRepresentable
                ((𝒮.bigAffineInclusion S).obj (D.obj I))),
            IsIso g ∧ g ≫ c.ι.app I ≫ hX.inv = t :=
  sorry

end AlgebraicGeometry.IsAffineFormalAlgebraicSpace
