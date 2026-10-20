module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.Sieves
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.InfinitesimalNeighbourhood.Transition
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Basic

/-!
# Completion of an algebraic space along a closed subspace

The completion `completionAlongSubspace i` of an algebraic space `X` along a
closed immersion `i : Z ⟶ X` is the fppf sheaf of morphisms into `X` that
fppf-locally factor through some infinitesimal neighbourhood
`Hom.InfinitesimalNeighbourhood.space i n = V(I^{n+1})`. This is the colimit of
the nested closed subspaces `Z_n` in fppf sheaves, not the presheaf of morphisms
that factor through a single neighbourhood globally.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TypeCat
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A Yoneda section of `X` factors through the `n`th infinitesimal neighbourhood
of a closed immersion `i : Z ⟶ X` when it lifts along
`Hom.InfinitesimalNeighbourhood.toAmbient i n`. -/
def factorsThroughNeighbourhood {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) {U : (Over S)ᵒᵖ}
    (x : X.functorOfPoints.obj U) : Prop :=
  ∃ y : (Hom.InfinitesimalNeighbourhood.space i n).functorOfPoints.obj U,
    (Hom.InfinitesimalNeighbourhood.toAmbient i n).app U y = x

/-- Factoring through the `n`th infinitesimal neighbourhood means lifting along
`Hom.InfinitesimalNeighbourhood.toAmbient i n`. -/
theorem factorsThroughNeighbourhood_iff {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) {U : (Over S)ᵒᵖ}
    (x : X.functorOfPoints.obj U) :
    factorsThroughNeighbourhood i n x ↔
      ∃ y : (Hom.InfinitesimalNeighbourhood.space i n).functorOfPoints.obj U,
        (Hom.InfinitesimalNeighbourhood.toAmbient i n).app U y = x :=
  sorry

/-- The image of a section of the `n`th infinitesimal neighbourhood under
`Hom.InfinitesimalNeighbourhood.toAmbient i n` factors through that
neighbourhood. -/
theorem factorsThroughNeighbourhood_toAmbient {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ)
    {U : (Over S)ᵒᵖ}
    (y : (Hom.InfinitesimalNeighbourhood.space i n).functorOfPoints.obj U) :
    factorsThroughNeighbourhood i n
      ((Hom.InfinitesimalNeighbourhood.toAmbient i n).app U y) :=
  sorry

/-- Factoring through an infinitesimal neighbourhood is stable under
precomposition with a morphism of schemes over `S`. -/
theorem factorsThroughNeighbourhood_map {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) {U V : (Over S)ᵒᵖ} (φ : U ⟶ V)
    {x : X.functorOfPoints.obj U} (hx : factorsThroughNeighbourhood i n x) :
    factorsThroughNeighbourhood i n (X.functorOfPoints.map φ x) :=
  sorry

/-- A Yoneda section of `X` fppf-locally factors through some infinitesimal
neighbourhood of `i` when it does so after restriction along an fppf cover. -/
def fppfLocallyFactorsThroughNeighbourhood {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] {U : (Over S)ᵒᵖ}
    (x : X.functorOfPoints.obj U) : Prop :=
  ∃ (ι : Type u) (cover : ι → Over S) (π : (j : ι) → cover j ⟶ U.unop),
    Sieve.ofArrows cover π ∈ Scheme.fppfTopology.over S U.unop ∧
      ∀ j, ∃ n, factorsThroughNeighbourhood i n
        (X.functorOfPoints.map (π j).op x)

/-- Fppf-local factorization is equivalent to factorization through neighbourhoods
on a covering family, with the neighbourhood allowed to vary over the cover. -/
theorem fppfLocallyFactorsThroughNeighbourhood_iff {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] {U : (Over S)ᵒᵖ}
    (x : X.functorOfPoints.obj U) :
    fppfLocallyFactorsThroughNeighbourhood i x ↔
      ∃ (ι : Type u) (cover : ι → Over S) (π : (j : ι) → cover j ⟶ U.unop),
        Sieve.ofArrows cover π ∈ Scheme.fppfTopology.over S U.unop ∧
          ∀ j, ∃ n, factorsThroughNeighbourhood i n
            (X.functorOfPoints.map (π j).op x) :=
  sorry

/-- A section that factors through some infinitesimal neighbourhood fppf-locally
factors through a neighbourhood. -/
theorem fppfLocallyFactorsThroughNeighbourhood.of_stage {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] {U : (Over S)ᵒᵖ}
    {x : X.functorOfPoints.obj U} (hx : ∃ n, factorsThroughNeighbourhood i n x) :
    fppfLocallyFactorsThroughNeighbourhood i x :=
  sorry

/-- Fppf-local factoring through an infinitesimal neighbourhood is stable under
precomposition with a morphism of schemes over `S`. -/
theorem fppfLocallyFactorsThroughNeighbourhood_map {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    {U V : (Over S)ᵒᵖ} (φ : U ⟶ V) {x : X.functorOfPoints.obj U}
    (hx : fppfLocallyFactorsThroughNeighbourhood i x) :
    fppfLocallyFactorsThroughNeighbourhood i (X.functorOfPoints.map φ x) :=
  sorry

/-- The completion of an algebraic space `X` along a closed subspace given by a
closed immersion `i : Z ⟶ X`, as the fppf sheaf of morphisms into `X` that
fppf-locally factor through some infinitesimal neighbourhood of `i`. -/
def completionAlongSubspace {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] : (Over S)ᵒᵖ ⥤ Type u where
  obj U :=
    { x : X.functorOfPoints.obj U // fppfLocallyFactorsThroughNeighbourhood i x }
  map φ :=
    ofHom fun x ↦
      ⟨X.functorOfPoints.map φ (Subtype.val x),
        fppfLocallyFactorsThroughNeighbourhood_map i φ x.property⟩
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    change X.functorOfPoints.map (𝟙 U) x.val = x.val
    rw [X.functorOfPoints.map_id]
    rfl
  map_comp φ ψ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    change X.functorOfPoints.map (φ ≫ ψ) x.val =
      X.functorOfPoints.map ψ (X.functorOfPoints.map φ x.val)
    rw [X.functorOfPoints.map_comp]
    rfl

/-- Sections of `completionAlongSubspace i` over `U` are the sections of
`X.functorOfPoints` that fppf-locally factor through some infinitesimal
neighbourhood of `i`. -/
theorem completionAlongSubspace_eq {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (U : (Over S)ᵒᵖ) :
    (completionAlongSubspace i).obj U =
      { x : X.functorOfPoints.obj U //
        fppfLocallyFactorsThroughNeighbourhood i x } :=
  sorry

/-- The completion along a closed subspace is an fppf sheaf on schemes over `S`. -/
theorem isSheaf_completionAlongSubspace {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (completionAlongSubspace i) :=
  sorry

/-- The completion of an algebraic space along a closed subspace is a formal
algebraic space. -/
instance instIsFormalAlgebraicSpace_completionAlongSubspace {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] :
    FormalAlgebraicSpace.IsFormalAlgebraicSpace (completionAlongSubspace i) :=
  sorry

/-- The coequalizer size condition: there exist objects `U`, `R` of `(Sch/S)_fppf`
and fppf-locally surjective maps from their representables onto the completion
and onto the fibre product of that atlas with itself. -/
theorem exists_presentation_completionAlongSubspace {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ (U R : Over S) (π : yoneda.obj U ⟶ completionAlongSubspace i)
      (σ : yoneda.obj R ⟶ pullback π π),
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) π ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ :=
  sorry

namespace completionAlongSubspace

/-- The canonical morphism `completionAlongSubspace i ⟶ X.functorOfPoints` from
the completion along the closed subspace. -/
def ι {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    completionAlongSubspace i ⟶ X.functorOfPoints where
  app _ := ofHom Subtype.val
  naturality := sorry

/-- Components of `ι i` are the subtype projections of
`completionAlongSubspace i`. -/
theorem ι_app {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : (Over S)ᵒᵖ) :
    (ι i).app U = ofHom Subtype.val :=
  sorry

/-- A Yoneda section of `X` fppf-locally factors through some infinitesimal
neighbourhood of `i` if and only if it lifts through `ι i`. -/
theorem exists_lift {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] {U : (Over S)ᵒᵖ} (x : X.functorOfPoints.obj U) :
    fppfLocallyFactorsThroughNeighbourhood i x ↔ ∃ y, (ι i).app U y = x :=
  sorry

/-- The canonical morphism from the `n`th infinitesimal neighbourhood of a closed
immersion into the formal completion along that closed subspace. -/
def fromStage {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] (n : ℕ) :
    (Hom.InfinitesimalNeighbourhood.space i n).functorOfPoints ⟶
      completionAlongSubspace i where
  app U :=
    ofHom fun y ↦
      ⟨(Hom.InfinitesimalNeighbourhood.toAmbient i n).app U y,
        fppfLocallyFactorsThroughNeighbourhood.of_stage i
          ⟨n, factorsThroughNeighbourhood_toAmbient i n y⟩⟩
  naturality := sorry

/-- Postcomposing `fromStage i n` with `ι i` recovers the neighbourhood inclusion
into `X`. -/
theorem fromStage_comp {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] (n : ℕ) :
    fromStage i n ≫ ι i = Hom.InfinitesimalNeighbourhood.toAmbient i n :=
  sorry

/-- Neighbourhood transitions are compatible with the cocone maps
`fromStage i n`. -/
theorem fromStage_comp_transition {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] {n m : ℕ} (h : n ≤ m) :
    NatTrans.vcomp (Hom.InfinitesimalNeighbourhood.transition i h)
      (fromStage i m) = fromStage i n :=
  sorry

end completionAlongSubspace

/-- The directed system of infinitesimal neighbourhoods of a closed immersion,
as functors of points. -/
def neighbourhoodSystem {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] : ℕ ⥤ (Over S)ᵒᵖ ⥤ Type u where
  obj n := (Hom.InfinitesimalNeighbourhood.space i n).functorOfPoints
  map f := Hom.InfinitesimalNeighbourhood.transition i (leOfHom f)
  map_id n := by
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    rfl
  map_comp {n m k} f g := by
    apply (cancel_mono (subschemeι (Hom.InfinitesimalNeighbourhood.ideal i k))).1
    change Hom.InfinitesimalNeighbourhood.transition i _ ≫ subschemeι _ =
      (Hom.InfinitesimalNeighbourhood.transition i _ ≫
        Hom.InfinitesimalNeighbourhood.transition i _) ≫ subschemeι _
    exact (inclusion_subschemeι
      (Hom.InfinitesimalNeighbourhood.ideal_le_of_le i (leOfHom (f ≫ g)))).trans
      ((Category.assoc _ _ _).trans
        ((congrArg
          (fun t ↦ Hom.InfinitesimalNeighbourhood.transition i (leOfHom f) ≫ t)
          (inclusion_subschemeι
            (Hom.InfinitesimalNeighbourhood.ideal_le_of_le i (leOfHom g)))).trans
          (inclusion_subschemeι
            (Hom.InfinitesimalNeighbourhood.ideal_le_of_le i (leOfHom f))))).symm

/-- Objects of `neighbourhoodSystem i` are the functors of points of the
infinitesimal neighbourhoods of `i`. -/
theorem neighbourhoodSystem_obj {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) :
    (neighbourhoodSystem i).obj n =
      (Hom.InfinitesimalNeighbourhood.space i n).functorOfPoints :=
  sorry

/-- The cocone of infinitesimal neighbourhoods with vertex
`completionAlongSubspace i`. -/
def fromStageCocone {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] : Cocone (neighbourhoodSystem i) where
  pt := completionAlongSubspace i
  ι :=
    { app := fun n ↦ completionAlongSubspace.fromStage i n
      naturality := sorry }

/-- Components of `fromStageCocone i` are the morphisms
`completionAlongSubspace.fromStage i n`. -/
theorem fromStageCocone_ι {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) :
    (fromStageCocone i).ι.app n = completionAlongSubspace.fromStage i n :=
  sorry

/-- A morphism from `completionAlongSubspace i` to an fppf sheaf is uniquely
determined by a compatible family of morphisms from the infinitesimal
neighbourhoods, so the completion is the colimit of the `Z_n` in fppf sheaves. -/
theorem existsUnique_desc_completionAlongSubspace {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (f : (n : ℕ) →
      (Hom.InfinitesimalNeighbourhood.space i n).functorOfPoints ⟶ F)
    (hf : ∀ {n m : ℕ} (h : n ≤ m),
      NatTrans.vcomp (Hom.InfinitesimalNeighbourhood.transition i h) (f m) =
        f n) :
    ∃! g : completionAlongSubspace i ⟶ F,
      ∀ n, completionAlongSubspace.fromStage i n ≫ g = f n :=
  sorry

/-- On test objects, `completionAlongSubspace.fromStage i n` is the image of
`Hom.InfinitesimalNeighbourhood.toAmbient i n` in the completion. -/
theorem completionAlongSubspace.fromStage_app {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] (n : ℕ) (U : (Over S)ᵒᵖ)
    (y : (Hom.InfinitesimalNeighbourhood.space i n).functorOfPoints.obj U) :
    (completionAlongSubspace.ι i).app U ((completionAlongSubspace.fromStage i n).app U y) =
      (Hom.InfinitesimalNeighbourhood.toAmbient i n).app U y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
