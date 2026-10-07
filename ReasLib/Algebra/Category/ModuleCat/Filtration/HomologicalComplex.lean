module

public import ReasLib.Algebra.Category.ModuleCat.Filtration.DifferentialObject
public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Functors

/-!
# Submodule Filtrations on Homological Complexes of Modules

This file packages decreasing families of submodules as filtered objects and extends the
construction degreewise to an arbitrary homological complex of `ModuleCat`.  The lower-level
map API applies to different source and target modules, so filtered complex differentials and
filtered complex maps use the same canonical construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe uR uM uι

namespace ModuleCat.SubmoduleFiltration

variable {R : Type uR} [Ring R]
variable {M N : Type uM}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A linear map preserves two decreasing submodule families when it maps each source stage
into the target stage with the same index. -/
def Preserves (f : M →ₗ[R] N) (F : ℤ → Submodule R M) (G : ℤ → Submodule R N) : Prop :=
  ∀ p : ℤ, Submodule.map f (F p) ≤ G p

/-- A filtration-preserving linear map sends an element of a source stage into the
corresponding target stage. -/
theorem map_mem (f : M →ₗ[R] N) (F : ℤ → Submodule R M) (G : ℤ → Submodule R N)
    (hf : Preserves f F G) (p : ℤ) (x : F p) : f x ∈ G p := sorry

/-- The restriction of a filtration-preserving linear map to the `p`-th submodules. -/
def stageLinearMap (f : M →ₗ[R] N) (F : ℤ → Submodule R M) (G : ℤ → Submodule R N)
    (hf : Preserves f F G) (p : ℤ) : F p →ₗ[R] G p :=
  LinearMap.codRestrict (G p) (f.domRestrict (F p)) (map_mem f F G hf p)

/-- The restricted stage map agrees with the original linear map on elements. -/
@[simp]
theorem stageLinearMap_apply (f : M →ₗ[R] N) (F : ℤ → Submodule R M)
    (G : ℤ → Submodule R N) (hf : Preserves f F G) (p : ℤ) (x : F p) :
    (stageLinearMap f F G hf p x : N) = f x := sorry

/-- A linear map taking one submodule into another factors through the canonical target
`ModuleCat` subobject. -/
theorem factors (f : M →ₗ[R] N) {S : Submodule R M} {T : Submodule R N}
    (hf : Submodule.map f S ≤ T) :
    ((ModuleCat.subobjectModule (ModuleCat.of R N)).symm T).Factors
      (((ModuleCat.subobjectModule (ModuleCat.of R M)).symm S).arrow ≫ ModuleCat.ofHom f) :=
  sorry

/-- Package a filtration-preserving linear map as a morphism between the filtered objects
defined by its source and target submodule families. -/
@[stacks 012B "filtered ModuleCat morphism from submodule families"]
noncomputable def hom (f : M →ₗ[R] N) (F : ℤ → Submodule R M) (G : ℤ → Submodule R N)
    (hF : Antitone F) (hG : Antitone G) (hf : Preserves f F G) :
    object F hF ⟶ object G hG where
  hom := ModuleCat.ofHom f
  preserves := fun p ↦ factors f (hf p)

/-- The underlying morphism of `hom` is the original linear map. -/
@[simp]
theorem hom_hom (f : M →ₗ[R] N) (F : ℤ → Submodule R M) (G : ℤ → Submodule R N)
    (hF : Antitone F) (hG : Antitone G) (hf : Preserves f F G) :
    (hom f F G hF hG hf).hom = ModuleCat.ofHom f := sorry

/-- The categorical stage map is characterized by restriction of the underlying map to the
two filtration stages. -/
@[simp]
theorem stageMap_arrow (f : M →ₗ[R] N) (F : ℤ → Submodule R M)
    (G : ℤ → Submodule R N) (hF : Antitone F) (hG : Antitone G)
    (hf : Preserves f F G) (p : ℤ) :
    (hom f F G hF hG hf).stageMap p ≫
        ((object G hG).filtration.stage p).arrow =
      ((object F hF).filtration.stage p).arrow ≫
        ModuleCat.ofHom f := sorry

/-- Under the canonical identifications of categorical stages with submodules, the stage map
is `stageLinearMap`. -/
theorem stageMap_eq (f : M →ₗ[R] N) (F : ℤ → Submodule R M) (G : ℤ → Submodule R N)
    (hF : Antitone F) (hG : Antitone G) (hf : Preserves f F G) (p : ℤ) :
    (ModuleCat.SubobjectModule.underlyingIso (ModuleCat.of R M) (F p)).inv ≫
        (hom f F G hF hG hf).stageMap p ≫
          (ModuleCat.SubobjectModule.underlyingIso (ModuleCat.of R N) (G p)).hom =
      ModuleCat.ofHom (stageLinearMap f F G hf p) := sorry

/-- The identity linear map preserves every submodule filtration. -/
theorem preserves_id (F : ℤ → Submodule R M) :
    Preserves (LinearMap.id : M →ₗ[R] M) F F := sorry

/-- Restricting the identity map to a filtration stage gives the identity map of that stage. -/
@[simp]
theorem stageLinearMap_id (F : ℤ → Submodule R M) (p : ℤ) :
    stageLinearMap (LinearMap.id : M →ₗ[R] M) F F (preserves_id F) p = LinearMap.id := sorry

/-- Packaging the identity linear map gives the identity filtered morphism. -/
@[simp]
theorem hom_id (F : ℤ → Submodule R M) (hF : Antitone F) :
    hom (LinearMap.id : M →ₗ[R] M) F F hF hF (preserves_id F) =
      𝟙 (object F hF) := sorry

section Composition

variable {P : Type uM} [AddCommGroup P] [Module R P]

/-- A composite of filtration-preserving linear maps preserves the source and target
filtrations. -/
theorem preserves_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (F : ℤ → Submodule R M) (G : ℤ → Submodule R N) (H : ℤ → Submodule R P)
    (hf : Preserves f F G) (hg : Preserves g G H) : Preserves (g.comp f) F H := sorry

/-- Restriction to a filtration stage commutes with composition of filtration-preserving
linear maps. -/
@[simp]
theorem stageLinearMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (F : ℤ → Submodule R M) (G : ℤ → Submodule R N) (H : ℤ → Submodule R P)
    (hf : Preserves f F G) (hg : Preserves g G H) (p : ℤ) :
    stageLinearMap (g.comp f) F H (preserves_comp f g F G H hf hg) p =
      (stageLinearMap g G H hg p).comp (stageLinearMap f F G hf p) := sorry

/-- Packaging filtration-preserving linear maps commutes with composition. -/
@[simp]
theorem hom_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (F : ℤ → Submodule R M) (G : ℤ → Submodule R N) (H : ℤ → Submodule R P)
    (hF : Antitone F) (hG : Antitone G) (hH : Antitone H)
    (hf : Preserves f F G) (hg : Preserves g G H) :
    hom (g.comp f) F H hF hH (preserves_comp f g F G H hf hg) =
      hom f F G hF hG hf ≫ hom g G H hG hH hg := sorry

end Composition

end ModuleCat.SubmoduleFiltration

namespace HomologicalComplex

variable {R : Type uR} [Ring R]
variable {ι : Type uι} {c : ComplexShape ι}

/-- A decreasing submodule filtration on every term of a homological complex, preserved by
all of its differentials. -/
@[stacks 012B "submodule filtration of a ModuleCat homological complex"]
structure SubmoduleFiltration (K : HomologicalComplex (ModuleCat.{uM} R) c) where
  /-- The `p`-th submodule in homological degree `i`. -/
  submodule : ∀ i : ι, ℤ → Submodule R (K.X i)
  /-- The filtration in every homological degree is decreasing. -/
  antitone (i : ι) : Antitone (submodule i)
  /-- Every differential preserves every filtration stage. -/
  d_preserves (i j : ι) : ModuleCat.SubmoduleFiltration.Preserves
    (K.d i j).hom (submodule i) (submodule j)

namespace SubmoduleFiltration

variable {K L Q : HomologicalComplex (ModuleCat.{uM} R) c}

/-- The filtered object carried by one term of a submodule-filtered homological complex. -/
noncomputable def term (F : SubmoduleFiltration K) (i : ι) :
    CategoryTheory.FilteredObject (ModuleCat.{uM} R) :=
  ModuleCat.SubmoduleFiltration.object (F.submodule i) (F.antitone i)

/-- The differential between two terms, packaged as a filtration-preserving morphism. -/
noncomputable def differential (F : SubmoduleFiltration K) (i j : ι) :
    F.term i ⟶ F.term j :=
  ModuleCat.SubmoduleFiltration.hom (K.d i j).hom
    (F.submodule i) (F.submodule j) (F.antitone i) (F.antitone j) (F.d_preserves i j)

/-- A forbidden differential remains zero after it is packaged as a filtered morphism. -/
theorem differential_shape (F : SubmoduleFiltration K) (i j : ι) (hij : ¬ c.Rel i j) :
    F.differential i j = 0 := sorry

/-- Consecutive packaged differentials have zero composite. -/
theorem differential_comp (F : SubmoduleFiltration K) (i j k : ι) :
    F.differential i j ≫ F.differential j k = 0 := sorry

/-- The homological complex in filtered `ModuleCat` objects defined by a degreewise submodule
filtration. -/
@[stacks 012L "filtered homological complex from submodule families"]
noncomputable def filtered (F : SubmoduleFiltration K) :
    HomologicalComplex (CategoryTheory.FilteredObject (ModuleCat.{uM} R)) c where
  X := F.term
  d := F.differential
  shape := differential_shape F
  d_comp_d' := fun i j k _ _ ↦ differential_comp F i j k

/-- The `i`-th term of `filtered F` is the filtered object defined by the submodules in degree
`i`. -/
@[simp]
theorem filtered_X (F : SubmoduleFiltration K) (i : ι) :
    F.filtered.X i = F.term i := sorry

/-- Forgetting the filtration from one term of `filtered F` recovers the original term. -/
@[simp]
theorem filtered_X_obj (F : SubmoduleFiltration K) (i : ι) :
    (F.filtered.X i).obj = K.X i := sorry

/-- The submodule represented by a stage of `filtered F` is the submodule specified by `F`. -/
@[simp]
theorem subobjectModule_stage (F : SubmoduleFiltration K) (i : ι) (p : ℤ) :
    ModuleCat.subobjectModule (K.X i) ((F.filtered.X i).filtration.stage p) =
      F.submodule i p := sorry

/-- The differential of `filtered F` is the canonical filtered differential constructed from
the corresponding differential of `K`. -/
@[simp]
theorem filtered_d (F : SubmoduleFiltration K) (i j : ι) :
    F.filtered.d i j = F.differential i j := sorry

/-- Forgetting the filtration from a differential of `filtered F` recovers the differential
of the original complex. -/
@[simp]
theorem filtered_d_hom (F : SubmoduleFiltration K) (i j : ι) :
    (F.filtered.d i j).hom = K.d i j := sorry

/-- Forgetting the filtration from the whole filtered complex recovers the original
homological complex. -/
theorem filtered_underlying (F : SubmoduleFiltration K) :
    CategoryTheory.HomologicalComplex.Filtered.underlying F.filtered = K := sorry

/-- A complex map preserves submodule filtrations when every component preserves every stage. -/
def Preserves (F : SubmoduleFiltration K) (G : SubmoduleFiltration L) (f : K ⟶ L) : Prop :=
  ∀ i : ι, ModuleCat.SubmoduleFiltration.Preserves
    (f.f i).hom (F.submodule i) (G.submodule i)

/-- The component of a filtration-preserving complex map between the corresponding filtered
terms. -/
noncomputable def termMap {F : SubmoduleFiltration K} {G : SubmoduleFiltration L}
    {f : K ⟶ L} (hf : Preserves F G f) (i : ι) : F.term i ⟶ G.term i :=
  ModuleCat.SubmoduleFiltration.hom (f.f i).hom
    (F.submodule i) (G.submodule i) (F.antitone i) (G.antitone i) (hf i)

/-- The filtered components of a filtration-preserving complex map commute with the filtered
differentials. -/
theorem termMap_comm {F : SubmoduleFiltration K} {G : SubmoduleFiltration L}
    {f : K ⟶ L} (hf : Preserves F G f) (i j : ι) :
    termMap hf i ≫ G.differential i j = F.differential i j ≫ termMap hf j := sorry

/-- Package a filtration-preserving complex map as a map of filtered homological complexes. -/
noncomputable def map {F : SubmoduleFiltration K} {G : SubmoduleFiltration L}
    {f : K ⟶ L} (hf : Preserves F G f) : F.filtered ⟶ G.filtered where
  f := termMap hf
  comm' := fun i j _ ↦ termMap_comm hf i j

/-- The underlying morphism of a component of `map hf` is the corresponding component of the
original complex map. -/
@[simp]
theorem map_f_hom {F : SubmoduleFiltration K} {G : SubmoduleFiltration L}
    {f : K ⟶ L} (hf : Preserves F G f) (i : ι) :
    ((map hf).f i).hom = f.f i := sorry

/-- The identity complex map preserves every submodule filtration. -/
theorem preserves_id (F : SubmoduleFiltration K) : Preserves F F (𝟙 K) := sorry

/-- The composite of filtration-preserving complex maps preserves the composite filtration. -/
theorem preserves_comp {F : SubmoduleFiltration K} {G : SubmoduleFiltration L}
    {H : SubmoduleFiltration Q} {f : K ⟶ L} {g : L ⟶ Q}
    (hf : Preserves F G f) (hg : Preserves G H g) : Preserves F H (f ≫ g) := sorry

/-- Packaging the identity as a filtered complex map gives the identity. -/
@[simp]
theorem map_id (F : SubmoduleFiltration K) : map (preserves_id F) = 𝟙 F.filtered := sorry

/-- Packaging a composite filtration-preserving map agrees with composing the packaged maps. -/
@[simp]
theorem map_comp {F : SubmoduleFiltration K} {G : SubmoduleFiltration L}
    {H : SubmoduleFiltration Q} {f : K ⟶ L} {g : L ⟶ Q}
    (hf : Preserves F G f) (hg : Preserves G H g) :
    map (preserves_comp hf hg) = map hf ≫ map hg := sorry

end SubmoduleFiltration

end HomologicalComplex
