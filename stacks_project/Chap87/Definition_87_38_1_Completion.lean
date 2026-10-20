/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlongSubspace

/-!
# Completion along a closed subspace

The completion, its infinitesimal-neighbourhood diagram, and its canonical maps
are provided by their shared mathematical owners.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TypeCat
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom.InfinitesimalNeighbourhood

/- For `n ≤ m`, the defining ideal of the `m`th infinitesimal neighbourhood is
contained in the defining ideal of the `n`th neighbourhood. -/
#check (ideal_le_of_le : ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] {n m : ℕ} (h : n ≤ m),
    ideal i m ≤ ideal i n)

/- The closed-subspace inclusion `Z_n ⟶ Z_m` of infinitesimal neighbourhoods
for `n ≤ m`. -/
#check (transition : ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] {n m : ℕ} (h : n ≤ m),
    space i n ⟶ space i m)

/- On underlying maps into the coborder, `transition i h` is the nested
closed-subspace inclusion of the neighbourhood ideals. -/
#check (transition_eq : ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] {n m : ℕ} (h : n ≤ m),
    transition i h = inclusion (ideal_le_of_le i h))

/- The transition `Z_n ⟶ Z_m` is a relative thickening: a closed immersion
inducing an isomorphism on reductions. -/
#check (instIsThickening_transition : ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] {n m : ℕ} (h : n ≤ m),
    IsThickening (transition i h))

/- Postcomposing a neighbourhood transition with `toAmbient` recovers the
earlier ambient inclusion. -/
#check (transition_comp_toAmbient : ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] {n m : ℕ} (h : n ≤ m),
    transition i h ≫ toAmbient i m = toAmbient i n)

end Hom.InfinitesimalNeighbourhood

/- A Yoneda section of `X` factors through the `n`th infinitesimal neighbourhood
of a closed immersion `i : Z ⟶ X` when it lifts along
`Hom.InfinitesimalNeighbourhood.toAmbient i n`. -/
#check (factorsThroughNeighbourhood : ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) {U : (Over S)ᵒᵖ}
    (x : X.functorOfPoints.obj U),
    Prop)

/- Factoring through the `n`th infinitesimal neighbourhood means lifting along
`Hom.InfinitesimalNeighbourhood.toAmbient i n`. -/
#check (factorsThroughNeighbourhood_iff : ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) {U : (Over S)ᵒᵖ}
    (x : X.functorOfPoints.obj U),
    factorsThroughNeighbourhood i n x ↔
      ∃ y : (Hom.InfinitesimalNeighbourhood.space i n).functorOfPoints.obj U,
        (Hom.InfinitesimalNeighbourhood.toAmbient i n).app U y = x)

/- The image of a section of the `n`th infinitesimal neighbourhood under
`Hom.InfinitesimalNeighbourhood.toAmbient i n` factors through that
neighbourhood. -/
#check (factorsThroughNeighbourhood_toAmbient : ∀ {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ)
    {U : (Over S)ᵒᵖ}
    (y : (Hom.InfinitesimalNeighbourhood.space i n).functorOfPoints.obj U),
    factorsThroughNeighbourhood i n
      ((Hom.InfinitesimalNeighbourhood.toAmbient i n).app U y))

/- Factoring through an infinitesimal neighbourhood is stable under
precomposition with a morphism of schemes over `S`. -/
#check (factorsThroughNeighbourhood_map : ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) {U V : (Over S)ᵒᵖ} (φ : U ⟶ V)
    {x : X.functorOfPoints.obj U} (hx : factorsThroughNeighbourhood i n x),
    factorsThroughNeighbourhood i n (X.functorOfPoints.map φ x))

/- A Yoneda section of `X` fppf-locally factors through some infinitesimal
neighbourhood of `i` when it does so after restriction along an fppf cover. -/
#check (fppfLocallyFactorsThroughNeighbourhood : ∀ {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] {U : (Over S)ᵒᵖ}
    (x : X.functorOfPoints.obj U),
    Prop)

/- Fppf-local factorization is equivalent to factorization through neighbourhoods
on a covering family, with the neighbourhood allowed to vary over the cover. -/
#check (fppfLocallyFactorsThroughNeighbourhood_iff : ∀ {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] {U : (Over S)ᵒᵖ}
    (x : X.functorOfPoints.obj U),
    fppfLocallyFactorsThroughNeighbourhood i x ↔
      ∃ (ι : Type u) (cover : ι → Over S) (π : (j : ι) → cover j ⟶ U.unop),
        Sieve.ofArrows cover π ∈ Scheme.fppfTopology.over S U.unop ∧
          ∀ j, ∃ n, factorsThroughNeighbourhood i n
            (X.functorOfPoints.map (π j).op x))

/- A section that factors through some infinitesimal neighbourhood fppf-locally
factors through a neighbourhood. -/
#check (fppfLocallyFactorsThroughNeighbourhood.of_stage : ∀ {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] {U : (Over S)ᵒᵖ}
    {x : X.functorOfPoints.obj U} (hx : ∃ n, factorsThroughNeighbourhood i n x),
    fppfLocallyFactorsThroughNeighbourhood i x)

/- Fppf-local factoring through an infinitesimal neighbourhood is stable under
precomposition with a morphism of schemes over `S`. -/
#check (fppfLocallyFactorsThroughNeighbourhood_map : ∀ {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    {U V : (Over S)ᵒᵖ} (φ : U ⟶ V) {x : X.functorOfPoints.obj U}
    (hx : fppfLocallyFactorsThroughNeighbourhood i x),
    fppfLocallyFactorsThroughNeighbourhood i (X.functorOfPoints.map φ x))

/- The completion of an algebraic space `X` along a closed subspace given by a
closed immersion `i : Z ⟶ X`, as the fppf sheaf of morphisms into `X` that
fppf-locally factor through some infinitesimal neighbourhood of `i`. -/
#check (completionAlongSubspace : ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i],
    (Over S)ᵒᵖ ⥤ Type u)

/- Sections of `completionAlongSubspace i` over `U` are the sections of
`X.functorOfPoints` that fppf-locally factor through some infinitesimal
neighbourhood of `i`. -/
#check (completionAlongSubspace_eq : ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (U : (Over S)ᵒᵖ),
    (completionAlongSubspace i).obj U =
      { x : X.functorOfPoints.obj U //
        fppfLocallyFactorsThroughNeighbourhood i x })

/- The completion along a closed subspace is an fppf sheaf on schemes over `S`. -/
#check (isSheaf_completionAlongSubspace : ∀ {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i],
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (completionAlongSubspace i))

/- The completion of an algebraic space along a closed subspace is a formal
algebraic space. -/
#check (instIsFormalAlgebraicSpace_completionAlongSubspace : ∀ {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i],
    FormalAlgebraicSpace.IsFormalAlgebraicSpace (completionAlongSubspace i))

/- The coequalizer size condition: there exist objects `U`, `R` of `(Sch/S)_fppf`
and fppf-locally surjective maps from their representables onto the completion
and onto the fibre product of that atlas with itself. -/
#check (exists_presentation_completionAlongSubspace : ∀ {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i],
    ∃ (U R : Over S) (π : yoneda.obj U ⟶ completionAlongSubspace i)
      (σ : yoneda.obj R ⟶ pullback π π),
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) π ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ)

namespace completionAlongSubspace

/- The canonical morphism `completionAlongSubspace i ⟶ X.functorOfPoints` from
the completion along the closed subspace. -/
#check (ι : ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i],
    completionAlongSubspace i ⟶ X.functorOfPoints)

/- Components of `ι i` are the subtype projections of
`completionAlongSubspace i`. -/
#check (ι_app : ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : (Over S)ᵒᵖ),
    (ι i).app U = ofHom Subtype.val)

/- A Yoneda section of `X` fppf-locally factors through some infinitesimal
neighbourhood of `i` if and only if it lifts through `ι i`. -/
#check (exists_lift : ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] {U : (Over S)ᵒᵖ} (x : X.functorOfPoints.obj U),
    fppfLocallyFactorsThroughNeighbourhood i x ↔ ∃ y, (ι i).app U y = x)

/- The canonical morphism from the `n`th infinitesimal neighbourhood of a closed
immersion into the formal completion along that closed subspace. -/
#check (fromStage : ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] (n : ℕ),
    (Hom.InfinitesimalNeighbourhood.space i n).functorOfPoints ⟶
      completionAlongSubspace i)

/- Postcomposing `fromStage i n` with `ι i` recovers the neighbourhood inclusion
into `X`. -/
#check (fromStage_comp : ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] (n : ℕ),
    fromStage i n ≫ ι i = Hom.InfinitesimalNeighbourhood.toAmbient i n)

/- Neighbourhood transitions are compatible with the cocone maps
`fromStage i n`. -/
#check (fromStage_comp_transition : ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] {n m : ℕ} (h : n ≤ m),
    NatTrans.vcomp (Hom.InfinitesimalNeighbourhood.transition i h)
      (fromStage i m) = fromStage i n)

end completionAlongSubspace

/- The directed system of infinitesimal neighbourhoods of a closed immersion,
as functors of points. -/
#check (neighbourhoodSystem : ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i],
    ℕ ⥤ (Over S)ᵒᵖ ⥤ Type u)

/- Objects of `neighbourhoodSystem i` are the functors of points of the
infinitesimal neighbourhoods of `i`. -/
#check (neighbourhoodSystem_obj : ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ),
    (neighbourhoodSystem i).obj n =
      (Hom.InfinitesimalNeighbourhood.space i n).functorOfPoints)

/- The cocone of infinitesimal neighbourhoods with vertex
`completionAlongSubspace i`. -/
#check (fromStageCocone : ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i],
    Cocone (neighbourhoodSystem i))

/- Components of `fromStageCocone i` are the morphisms
`completionAlongSubspace.fromStage i n`. -/
#check (fromStageCocone_ι : ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ),
    (fromStageCocone i).ι.app n = completionAlongSubspace.fromStage i n)

/- A morphism from `completionAlongSubspace i` to an fppf sheaf is uniquely
determined by a compatible family of morphisms from the infinitesimal
neighbourhoods, so the completion is the colimit of the `Z_n` in fppf sheaves. -/
#check (existsUnique_desc_completionAlongSubspace : ∀ {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (f : (n : ℕ) →
      (Hom.InfinitesimalNeighbourhood.space i n).functorOfPoints ⟶ F)
    (hf : ∀ {n m : ℕ} (h : n ≤ m),
      NatTrans.vcomp (Hom.InfinitesimalNeighbourhood.transition i h) (f m) =
        f n),
    ∃! g : completionAlongSubspace i ⟶ F,
      ∀ n, completionAlongSubspace.fromStage i n ≫ g = f n)

/- On test objects, `completionAlongSubspace.fromStage i n` is the image of
`Hom.InfinitesimalNeighbourhood.toAmbient i n` in the completion. -/
#check (completionAlongSubspace.fromStage_app : ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] (n : ℕ) (U : (Over S)ᵒᵖ)
    (y : (Hom.InfinitesimalNeighbourhood.space i n).functorOfPoints.obj U),
    (completionAlongSubspace.ι i).app U ((completionAlongSubspace.fromStage i n).app U y) =
      (Hom.InfinitesimalNeighbourhood.toAmbient i n).app U y)

end AlgebraicGeometry.AlgebraicSpace
