module

public import stacks_project.Chap108.Lemma_108_4_9_AtlasCoverSurjectivity

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site

/-- A single etale surjection is an actual cover in the over-scheme pretopology. -/
theorem overEtale_singleton_mem {S : Scheme.{u}} {U V : Over S} (f : U ⟶ V)
    (het : AlgebraicGeometry.Etale f.left) (hsur : AlgebraicGeometry.Surjective f.left) :
    Presieve.singleton f ∈ S.overPretopology (@AlgebraicGeometry.Etale) V := by
  let cov : V.left.Cover (Scheme.precoverage (@AlgebraicGeometry.Etale)) :=
    Scheme.Cover.mkOfCovers PUnit.{u + 1} (fun _ ↦ U.left) (fun _ ↦ f.left)
      (fun x ↦ ⟨PUnit.unit, hsur.surj x⟩) (fun _ ↦ het)
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI (i : cov.I₀) : (cov.X i).Over S := ⟨U.hom⟩
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI (i : cov.I₀) : (cov.f i).IsOver S := ⟨Over.w f⟩
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI : cov.Over S := {}
  refine ⟨cov, inferInstance, ?_⟩
  exact (Presieve.ofArrows_pUnit f).symm

/-- A u-indexed, jointly surjective family of etale over-morphisms is a cover. -/
theorem overEtale_ofArrows_mem {S : Scheme.{u}} {I : Type u}
    (U : I → Over S) (V : Over S) (f : ∀ i, U i ⟶ V)
    (het : ∀ i, AlgebraicGeometry.Etale (f i).left)
    (hsur : ∀ x : V.left, ∃ i y, (f i).left y = x) :
    Presieve.ofArrows U f ∈ S.overPretopology (@AlgebraicGeometry.Etale) V := by
  let cov : V.left.Cover (Scheme.precoverage (@AlgebraicGeometry.Etale)) :=
    Scheme.Cover.mkOfCovers I (fun i ↦ (U i).left) (fun i ↦ (f i).left) hsur het
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI (i : cov.I₀) : (cov.X i).Over S := ⟨(U i).hom⟩
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI (i : cov.I₀) : (cov.f i).IsOver S := ⟨Over.w (f i)⟩
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI : cov.Over S := {}
  exact ⟨cov, inferInstance, rfl⟩

/-- The original comap site accepts the corresponding actual chart covering family. -/
theorem spaceEtale_ofArrows_mem {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type u}
    (U : I → AlgebraicGeometry.AlgebraicSpace.smallEtaleSite X)
    (V : AlgebraicGeometry.AlgebraicSpace.smallEtaleSite X) (f : ∀ i, U i ⟶ V)
    (het : ∀ i, AlgebraicGeometry.Etale (f i).left.left)
    (hsur : ∀ x : V.left.left, ∃ i y, (f i).left.left y = x) :
    Presieve.ofArrows U f ∈ AlgebraicGeometry.AlgebraicSpace.smallEtalePrecoverage X V := by
  change (Presieve.ofArrows U f).map
    (AlgebraicGeometry.AlgebraicSpace.smallEtaleToOver X) ∈
      (S.overPretopology (@AlgebraicGeometry.Etale)).toPrecoverage V.left
  rw [Presieve.map_ofArrows]
  exact overEtale_ofArrows_mem (fun i ↦ (U i).left) V.left (fun i ↦ (f i).left) het hsur

/-- The actual comap precoverage of the original space accepts that same singleton. -/
theorem spaceEtale_singleton_mem {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V : AlgebraicGeometry.AlgebraicSpace.smallEtaleSite X} (f : U ⟶ V)
    (het : AlgebraicGeometry.Etale f.left.left)
    (hsur : AlgebraicGeometry.Surjective f.left.left) :
    Presieve.singleton f ∈ AlgebraicGeometry.AlgebraicSpace.smallEtalePrecoverage X V := by
  change (Presieve.singleton f).map
    (AlgebraicGeometry.AlgebraicSpace.smallEtaleToOver X) ∈
      (S.overPretopology (@AlgebraicGeometry.Etale)).toPrecoverage V.left
  rw [Presieve.map_singleton]
  exact overEtale_singleton_mem f.left het hsur

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
  (V : AlgebraicGeometry.AlgebraicSpace.smallEtaleSite X)

/-- The projection of the atlas pullback to the atlas is etale for a test object of X_et. -/
theorem atlasPullbackToAtlasEtale :
    AlgebraicGeometry.Etale (atlasPullbackToAtlas X V.left V.hom).left :=
  (presheaf_of_spaceEtale V.hom V.prop).property (atlasMap X)
    (yoneda.map (atlasPullbackToSource X V.left V.hom))
    (atlasPullbackToAtlas X V.left V.hom) (atlasPullbackSquare X V.left V.hom).flip

/-- The pullback scheme is a genuine chart of the chosen atlas. -/
noncomputable def atlasPullbackChart : (atlasScheme X).left.Etale :=
  MorphismProperty.Over.mk ⊤ (atlasPullbackToAtlas X V.left V.hom).left
    (atlasPullbackToAtlasEtale X V)

/-- The base comparison is the identity on the actual pullback scheme. -/
noncomputable def atlasPullbackBaseIso :
    (atlasUnderlying X).obj (atlasPullbackChart X V) ≅ atlasPullback X V.left V.hom :=
  Over.isoMk (Iso.refl _) (by
    exact (Category.id_comp _).trans (Over.w (atlasPullbackToAtlas X V.left V.hom)).symm)

/-- Transporting the atlas projection along the identity base comparison recovers the chart map. -/
theorem atlasPullbackBaseIso_comp :
    (atlasPullbackBaseIso X V).hom ≫ atlasPullbackToAtlas X V.left V.hom =
      chartToAtlas X (atlasPullbackChart X V) := by
  apply Over.OverMorphism.ext
  exact Category.id_comp _

/-- The actual etale chart maps back to the original test object in X_et. -/
noncomputable def atlasChartToTest :
    (atlasEtaleFunctor X).obj (atlasPullbackChart X V) ⟶ V :=
  MorphismProperty.CostructuredArrow.homMk
    ((atlasPullbackBaseIso X V).hom ≫ atlasPullbackToSource X V.left V.hom) trivial (by
      change yoneda.map ((atlasPullbackBaseIso X V).hom ≫ atlasPullbackToSource X V.left V.hom) ≫
        V.hom = chartMap X (atlasPullbackChart X V)
      erw [CategoryTheory.Functor.map_comp, Category.assoc,
        ← (atlasPullbackSquare X V.left V.hom).w, ← Category.assoc,
        ← CategoryTheory.Functor.map_comp, atlasPullbackBaseIso_comp]
      rfl)

/-- The chart-to-test map is etale; its identity base comparison changes no scheme map. -/
theorem atlasChartToTestEtale : AlgebraicGeometry.Etale (atlasChartToTest X V).left.left := by
  change AlgebraicGeometry.Etale (𝟙 _ ≫ (atlasPullbackToSource X V.left V.hom).left)
  simpa only [Category.id_comp] using atlasPullbackToSourceEtale X V.left V.hom

/-- The actual map from the atlas chart surjects onto the original test scheme. -/
theorem atlasChartToTestSurjective : AlgebraicGeometry.Surjective (atlasChartToTest X V).left.left := by
  change AlgebraicGeometry.Surjective (𝟙 _ ≫ (atlasPullbackToSource X V.left V.hom).left)
  simpa only [Category.id_comp] using atlasPullbackToSourceSurjective X V.left V.hom

/-- Every original test object has a covering by an actual chart of the input atlas. -/
theorem atlasChartToTestCover :
    Sieve.generate (Presieve.singleton (atlasChartToTest X V)) ∈
      AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X V :=
  Precoverage.generate_mem_toGrothendieck
    (spaceEtale_singleton_mem (atlasChartToTest X V)
      (atlasChartToTestEtale X V) (atlasChartToTestSurjective X V))

/-- Cover density in the original X_et site, proved from the input's actual atlas. -/
theorem atlasEtaleFunctorCoverDense :
    (atlasEtaleFunctor X).IsCoverDense (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X) :=
  Functor.isCoverDense_of_generate_singleton_functor_π_mem _ _
    (fun V ↦ ⟨atlasPullbackChart X V, atlasChartToTest X V, atlasChartToTestCover X V⟩)

/-- The chart functor preserves covering sieves, using actual u-indexed scheme covers. -/
theorem atlasEtaleFunctorCoverPreserving :
    CoverPreserving (atlasScheme X).left.smallEtaleTopology
      (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X) (atlasEtaleFunctor X) where
  cover_preserve {W} {T} hT := by
    have hpoints : ∀ x : W.left, ∃ (Y : (atlasScheme X).left.Etale) (f : Y ⟶ W) (y : Y.left),
        T f ∧ AlgebraicGeometry.Etale f.left ∧ f.left y = x := by
      apply (Scheme.mem_toGrothendieck_smallPretopology
        (P := @AlgebraicGeometry.Etale) (Q := @AlgebraicGeometry.Etale) W T).1
      simpa only [← Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl]
        using! hT
    choose chart morph point hmem het hpoint using hpoints
    have hcover := spaceEtale_ofArrows_mem
      (fun x ↦ (atlasEtaleFunctor X).obj (chart x)) ((atlasEtaleFunctor X).obj W)
      (fun x ↦ (atlasEtaleFunctor X).map (morph x)) het (fun x ↦ ⟨x, point x, hpoint x⟩)
    apply (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X).superset_covering _
      (Precoverage.generate_mem_toGrothendieck hcover)
    apply (Sieve.generate_le_iff _ _).2
    rintro domain arrow ⟨x⟩
    exact ⟨chart x, morph x, 𝟙 _, hmem x, (Category.id_comp _).symm⟩

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site
