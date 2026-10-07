module

public import ReasLib.AlgebraicGeometry.Scheme.IndQuasiAffine.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.OpenImmersion.Lift
public import ReasLib.AlgebraicGeometry.Scheme.QuasiAffine.Characterization
public import ReasLib.AlgebraicGeometry.Scheme.Topology.Spectral
public import ReasLib.Topology.CompactOpen.Intersection
public import ReasLib.Topology.Spectral.CompactOpenIntersection

@[expose] public section

open CategoryTheory TopologicalSpace Topology
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IsIndQuasiAffine

/-- Every compact-open stage in a directed presentation of `Set.range i` contains that range. -/
private theorem stageRangeSubsetStage
    {X E : Scheme.{u}} [X.IsIndQuasiAffine] (i : E ⟶ X)
    {S : Set (CompactOpens X)}
    (hS : IsCompactOpenDirectedIntersection (Set.range i) S) (U : S) :
    Set.range i ⊆ (U.1 : Set X) := by
  intro x hx
  exact hS.mem hx U.2

/-- A compact-open stage regarded as an ordinary open subscheme. -/
private def stageOpen
    {X : Scheme.{u}} [X.IsIndQuasiAffine]
    {S : Set (CompactOpens X)} (U : S) : X.Opens :=
  ⟨U.1, CompactOpens.isOpen U.1⟩

/-- The factorization of a morphism through a compact-open stage containing its range. -/
private noncomputable def stageFactor
    {X E : Scheme.{u}} [X.IsIndQuasiAffine] (i : E ⟶ X)
    {S : Set (CompactOpens X)}
    (hS : IsCompactOpenDirectedIntersection (Set.range i) S) (U : S) :
    E ⟶ (stageOpen (X := X) U).toScheme :=
  IsOpenImmersion.lift (stageOpen (X := X) U).ι i
    (by
      rw [(stageOpen (X := X) U).range_ι]
      exact stageRangeSubsetStage (i := i) hS U)

/-- Composing a compact-open stage factorization with the stage inclusion recovers the original
morphism. -/
private theorem stageFactor_fac
    {X E : Scheme.{u}} [X.IsIndQuasiAffine] (i : E ⟶ X)
    {S : Set (CompactOpens X)}
    (hS : IsCompactOpenDirectedIntersection (Set.range i) S) (U : S) :
    stageFactor i hS U ≫ (stageOpen (X := X) U).ι = i := by
  simpa [stageFactor] using
    IsOpenImmersion.lift_fac (stageOpen (X := X) U).ι i
      (stageRangeSubsetStage (i := i) hS U)

/-- Every compact-open subscheme of an ind-quasi-affine scheme is quasi-affine. -/
private theorem stageIsQuasiAffine
    {X E : Scheme.{u}} [X.IsIndQuasiAffine] (i : E ⟶ X)
    {S : Set (CompactOpens X)}
    (_hS : IsCompactOpenDirectedIntersection (Set.range i) S) (U : S) :
    (stageOpen (X := X) U).toScheme.IsQuasiAffine := by
  simpa using
    (AlgebraicGeometry.Scheme.IsIndQuasiAffine.quasiAffine_of_isCompact
      (X := X) (stageOpen (X := X) U) (CompactOpens.isCompact U.1))

/-- The canonical morphism from a compact-open stage to the spectrum of its global sections is
a quasi-compact open immersion. -/
private theorem stageToSpecΓ_quasiCompact_and_isOpenImmersion
    {X E : Scheme.{u}} [X.IsIndQuasiAffine] (i : E ⟶ X)
    {S : Set (CompactOpens X)}
    (hS : IsCompactOpenDirectedIntersection (Set.range i) S) (U : S) :
    QuasiCompact (stageOpen (X := X) U).toScheme.toSpecΓ ∧
      IsOpenImmersion (stageOpen (X := X) U).toScheme.toSpecΓ := by
  simpa using
    (AlgebraicGeometry.Scheme.isQuasiAffine_iff_toSpecΓ
      (stageOpen (X := X) U).toScheme).mp
      (stageIsQuasiAffine (i := i) hS U)

/-- A compact-open stage factorization is compatible with canonical morphisms to spectra of
global sections. -/
private theorem stageFactor_comp_toSpecΓ
    {X E : Scheme.{u}} [X.IsIndQuasiAffine] (i : E ⟶ X)
    {S : Set (CompactOpens X)}
    (hS : IsCompactOpenDirectedIntersection (Set.range i) S) (U : S) :
    stageFactor i hS U ≫ (stageOpen (X := X) U).toScheme.toSpecΓ =
      E.toSpecΓ ≫ Spec.map (stageFactor i hS U).appTop := by
  simpa using Scheme.toSpecΓ_naturality (stageFactor i hS U)

/-- Factoring a topological embedding through an open subscheme preserves the embedding
property. -/
private theorem stageFactor_isEmbedding
    {X E : Scheme.{u}} [X.IsIndQuasiAffine] (i : E ⟶ X) (h_i : IsEmbedding i)
    {S : Set (CompactOpens X)}
    (hS : IsCompactOpenDirectedIntersection (Set.range i) S) (U : S) :
    IsEmbedding (stageFactor i hS U) := by
  have hcomp : ((stageOpen (X := X) U).ι) ∘ stageFactor i hS U = i := by
    funext e
    simpa using congrArg (fun k : E ⟶ X ↦ k e) (stageFactor_fac (i := i) hS U)
  refine IsEmbedding.of_comp (stageFactor i hS U).continuous
    ((stageOpen (X := X) U).ι).continuous ?_
  exact hcomp ▸ h_i

/-- Postcomposing the canonical map with the spectrum map of a compact-open stage factorization
gives a topological embedding. -/
private theorem toSpecΓ_comp_specMap_stageFactor_isEmbedding
    {X E : Scheme.{u}} [X.IsIndQuasiAffine] (i : E ⟶ X) (h_i : IsEmbedding i)
    {S : Set (CompactOpens X)}
    (hS : IsCompactOpenDirectedIntersection (Set.range i) S) (U : S) :
    IsEmbedding (E.toSpecΓ ≫ Spec.map (stageFactor i hS U).appTop) := by
  have hStageOpen :
      IsOpenImmersion (stageOpen (X := X) U).toScheme.toSpecΓ :=
    (stageToSpecΓ_quasiCompact_and_isOpenImmersion (i := i) hS U).2
  rw [← stageFactor_comp_toSpecΓ (i := i) hS U]
  exact ((stageOpen (X := X) U).toScheme.toSpecΓ).isOpenEmbedding.toIsEmbedding.comp
    (stageFactor_isEmbedding (i := i) h_i hS U)

/-- A directed compact-open intersection presentation of the range of a topological embedding
into an ind-quasi-affine scheme forces the canonical map to global sections to be an embedding. -/
theorem isEmbedding_toSpecΓ_of_isCompactOpenDirectedIntersection
    {X E : Scheme.{u}} [X.IsIndQuasiAffine] (i : E ⟶ X) (h_i : IsEmbedding i)
    {S : Set (CompactOpens X)}
    (hS : IsCompactOpenDirectedIntersection (Set.range i) S) :
    IsEmbedding E.toSpecΓ := by
  let U : S := ⟨hS.nonempty.choose, hS.nonempty.choose_spec⟩
  refine IsEmbedding.of_comp E.toSpecΓ.continuous
    (Spec.map (stageFactor i hS U).appTop).continuous ?_
  simpa [Function.comp] using
    toSpecΓ_comp_specMap_stageFactor_isEmbedding (i := i) h_i hS U

/-- If a scheme is embedded as a nonempty intersection of compact opens in an ind-quasi-affine
scheme, its canonical morphism to the spectrum of global sections is a topological embedding and
induces isomorphisms on all stalks. -/
theorem toSpecΓ_isLocallyRingedEmbedding
    {X E : Scheme.{u}} [X.IsIndQuasiAffine] (i : E ⟶ X)
    (h_i : IsEmbedding i) [∀ e : E, IsIso (i.stalkMap e)]
    (h_range : ∃ S : Set (CompactOpens X), S.Nonempty ∧ Set.range i = ⋂ U ∈ S, (U : Set X)) :
    IsEmbedding E.toSpecΓ ∧ ∀ e : E, IsIso (E.toSpecΓ.stalkMap e) := by
  rcases h_range with ⟨S, hS_nonempty, hS_eq⟩
  let U : CompactOpens X := hS_nonempty.choose
  let V : X.Opens := ⟨U, CompactOpens.isOpen U⟩
  have hRangeSubset : Set.range i ⊆ (V : Set X) := by
    intro x hx
    have hx' : x ∈ ⋂ U ∈ S, (U : Set X) := by
      simpa [hS_eq] using hx
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hx' U) hS_nonempty.choose_spec
  have hRangeToV : Set.range i ⊆ Set.range V.ι := by
    rw [V.range_ι]
    exact hRangeSubset
  let jU : E ⟶ V.toScheme := IsOpenImmersion.lift V.ι i hRangeToV
  have hjU_fac : jU ≫ V.ι = i := by
    simpa [jU] using IsOpenImmersion.lift_fac V.ι i hRangeToV
  have hjU_comp : V.ι ∘ jU = i := by
    funext e
    simpa using congrArg (fun k : E ⟶ X ↦ k e) hjU_fac
  have hjU_emb : IsEmbedding jU := by
    refine IsEmbedding.of_comp jU.continuous V.ι.continuous ?_
    exact hjU_comp ▸ h_i
  have hV_quasiAffine : V.toScheme.IsQuasiAffine := by
    simpa [V] using
      (AlgebraicGeometry.Scheme.IsIndQuasiAffine.quasiAffine_of_isCompact
        (X := X) V (CompactOpens.isCompact U))
  have hV_openImm : IsOpenImmersion V.toScheme.toSpecΓ :=
    (AlgebraicGeometry.Scheme.isQuasiAffine_iff_toSpecΓ V.toScheme).mp hV_quasiAffine |>.2
  have hjU_toSpecΓ_emb : IsEmbedding (jU ≫ V.toScheme.toSpecΓ) := by
    exact (V.toScheme.toSpecΓ).isOpenEmbedding.toIsEmbedding.comp hjU_emb
  have hjU_toSpecΓ :
      jU ≫ V.toScheme.toSpecΓ = E.toSpecΓ ≫ Spec.map jU.appTop := by
    simpa [jU] using Scheme.toSpecΓ_naturality jU
  have hjU_toSpecΓ_comp :
      V.toScheme.toSpecΓ ∘ jU = (Spec.map jU.appTop) ∘ E.toSpecΓ := by
    funext e
    simpa using congrArg (fun k : E ⟶ Spec Γ(V.toScheme, ⊤) ↦ k e) hjU_toSpecΓ
  refine ⟨?_, ?_⟩
  · refine IsEmbedding.of_comp E.toSpecΓ.continuous (Spec.map jU.appTop).continuous ?_
    exact hjU_toSpecΓ_comp ▸ hjU_toSpecΓ_emb
  have hjU_stalkIso (e : E) : IsIso (jU.stalkMap e) := by
    simpa [jU] using IsOpenImmersion.lift_stalkMap_isIso V.ι i hRangeToV e
  intro e
  sorry

/-- The canonical morphism to the spectrum of global sections is a topological embedding under
a nonempty compact-open intersection presentation inside an ind-quasi-affine scheme. -/
theorem isEmbedding_toSpecΓ
    {X E : Scheme.{u}} [X.IsIndQuasiAffine] (i : E ⟶ X)
    (h_i : IsEmbedding i) [∀ e : E, IsIso (i.stalkMap e)]
    (h_range : ∃ S : Set (CompactOpens X), S.Nonempty ∧ Set.range i = ⋂ U ∈ S, (U : Set X)) :
    IsEmbedding E.toSpecΓ :=
  (toSpecΓ_isLocallyRingedEmbedding i h_i h_range).1

/-- The canonical morphism to the spectrum of global sections induces an isomorphism on every
stalk under a nonempty compact-open intersection presentation inside an ind-quasi-affine scheme. -/
theorem isIso_toSpecΓ_stalkMap
    {X E : Scheme.{u}} [X.IsIndQuasiAffine] (i : E ⟶ X)
    (h_i : IsEmbedding i) [∀ e : E, IsIso (i.stalkMap e)]
    (h_range : ∃ S : Set (CompactOpens X), S.Nonempty ∧ Set.range i = ⋂ U ∈ S, (U : Set X))
    (e : E) :
    IsIso (E.toSpecΓ.stalkMap e) :=
  (toSpecΓ_isLocallyRingedEmbedding i h_i h_range).2 e

/-- The image of the canonical morphism to the spectrum of global sections is a nonempty
intersection of compact opens when the scheme has such a presentation inside an ind-quasi-affine
scheme. -/
theorem exists_compactOpens_range_toSpecΓ
    {X E : Scheme.{u}} [X.IsIndQuasiAffine] (i : E ⟶ X)
    (h_i : IsEmbedding i) [∀ e : E, IsIso (i.stalkMap e)]
    (h_range : ∃ S : Set (CompactOpens X), S.Nonempty ∧ Set.range i = ⋂ U ∈ S, (U : Set X)) :
    ∃ T : Set (CompactOpens (Spec Γ(E, ⊤))),
      T.Nonempty ∧ Set.range E.toSpecΓ = ⋂ V ∈ T, (V : Set (Spec Γ(E, ⊤))) := by
  sorry

/-- The image of the canonical morphism to the spectrum of global sections admits a directed
compact-open intersection presentation. -/
theorem range_toSpecΓ_isCompactOpenDirectedIntersection
    {X E : Scheme.{u}} [X.IsIndQuasiAffine] (i : E ⟶ X)
    (h_i : IsEmbedding i) [∀ e : E, IsIso (i.stalkMap e)]
    (h_range : ∃ S : Set (CompactOpens X), S.Nonempty ∧ Set.range i = ⋂ U ∈ S, (U : Set X)) :
    ∃ T : Set (CompactOpens (Spec Γ(E, ⊤))),
      IsCompactOpenDirectedIntersection (Set.range E.toSpecΓ) T := by
  rcases exists_compactOpens_range_toSpecΓ i h_i h_range with ⟨T, _, hT⟩
  refine ((compactGeneralizingSubset_tfae
    (X := Spec Γ(E, ⊤)) (Set.range E.toSpecΓ)).out 3 4).mp ?_
  exact show ∃ T : Set (CompactOpens (Spec Γ(E, ⊤))),
    Set.range E.toSpecΓ = ⋂ V ∈ T, (V : Set (Spec Γ(E, ⊤))) from ⟨T, hT⟩

/-- If an ambient open is contained in an embedded compact-open intersection, then its image
under the canonical morphism to the spectrum of global sections is open. -/
theorem isOpen_image_toSpecΓ
    {X E : Scheme.{u}} [X.IsIndQuasiAffine] (i : E ⟶ X)
    (h_i : IsEmbedding i) [∀ e : E, IsIso (i.stalkMap e)]
    (h_range : ∃ S : Set (CompactOpens X), S.Nonempty ∧ Set.range i = ⋂ U ∈ S, (U : Set X))
    (W : X.Opens) (hW : (W : Set X) ⊆ Set.range i) :
    IsOpen (E.toSpecΓ '' (i ⁻¹' (W : Set X))) := by
  sorry

end AlgebraicGeometry.Scheme.IsIndQuasiAffine
