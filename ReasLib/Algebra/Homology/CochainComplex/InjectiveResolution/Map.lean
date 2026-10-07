module

public import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution.Definition
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Variable.Map

/-!
# Maps of Injective Resolutions

This file specializes the neutral cross-object right-resolution map to bounded-below injective
models.  It packages the comparison square used by downstream derived and spectral-sequence
constructions.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex.InjectiveResolution

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- A map of injective resolutions lying over a cochain map. -/
@[stacks 013I "map of injective resolutions"]
abbrev Map {K L : CochainComplex 𝒜 ℤ} (f : K ⟶ L)
    (I : InjectiveResolution K) (J : InjectiveResolution L) :=
  Plus.TermsIn.QuasiIsoTo.Map f I J

namespace Map

variable {K L M : CochainComplex 𝒜 ℤ} {f : K ⟶ L} {g : L ⟶ M}
  {I : InjectiveResolution K} {J : InjectiveResolution L}
  {H : InjectiveResolution M}

variable {N : CochainComplex 𝒜 ℤ} {h : M ⟶ N} {T : InjectiveResolution N}

/-- The morphism between bounded-below injective models. -/
abbrev modelHom (m : Map f I J) : I.model ⟶ J.model :=
  Plus.TermsIn.QuasiIsoTo.Map.modelHom m

/-- The cochain map between the resolving complexes. -/
abbrev hom (m : Map f I J) : I.complex ⟶ J.complex :=
  Plus.TermsIn.QuasiIsoTo.Map.hom m

/-- Construct a map of injective resolutions from its morphism of injective models and
comparison square. -/
def mk (modelHom : I.model ⟶ J.model)
    (naturality : I.ι ≫ (InjectivePlus.ι 𝒜).map modelHom = f ≫ J.ι) : Map f I J :=
  Plus.TermsIn.QuasiIsoTo.Map.mk modelHom naturality

/-- The named constructor retains the supplied morphism between injective models. -/
@[simp]
theorem mk_modelHom (modelHom : I.model ⟶ J.model)
    (naturality : I.ι ≫ (InjectivePlus.ι 𝒜).map modelHom = f ≫ J.ι) :
    (mk modelHom naturality).modelHom = modelHom := sorry

/-- The cochain map of the named constructor is induced by the injective-model inclusion. -/
@[simp]
theorem mk_hom (modelHom : I.model ⟶ J.model)
    (naturality : I.ι ≫ (InjectivePlus.ι 𝒜).map modelHom = f ≫ J.ι) :
    (mk modelHom naturality).hom = (InjectivePlus.ι 𝒜).map modelHom := sorry

/-- Maps of injective resolutions are determined by their morphisms of injective models. -/
@[ext]
theorem ext {m n : Map f I J} (h : m.modelHom = n.modelHom) : m = n := sorry

/-- A map of injective resolutions commutes with the comparison maps. -/
@[reassoc]
theorem ι_naturality (m : Map f I J) : I.ι ≫ m.hom = f ≫ J.ι := sorry

/-- The identity map of an injective resolution. -/
abbrev id (I : InjectiveResolution K) : Map (𝟙 K) I I :=
  Plus.TermsIn.QuasiIsoTo.Map.id I

/-- The identity injective-resolution map has identity model morphism. -/
@[simp]
theorem id_modelHom (I : InjectiveResolution K) : (id I).modelHom = 𝟙 I.model := sorry

/-- The identity injective-resolution map has identity underlying cochain map. -/
@[simp]
theorem id_hom (I : InjectiveResolution K) : (id I).hom = 𝟙 I.complex := sorry

/-- Compose maps of injective resolutions. -/
abbrev comp (m : Map f I J) (n : Map g J H) : Map (f ≫ g) I H :=
  Plus.TermsIn.QuasiIsoTo.Map.comp m n

/-- Composition of injective-resolution maps composes their model morphisms. -/
@[simp]
theorem comp_modelHom (m : Map f I J) (n : Map g J H) :
    (comp m n).modelHom = m.modelHom ≫ n.modelHom := sorry

/-- Composition of injective-resolution maps composes their underlying cochain maps. -/
@[simp]
theorem comp_hom (m : Map f I J) (n : Map g J H) :
    (comp m n).hom = m.hom ≫ n.hom := sorry

/-- Reindex a map of injective resolutions along an equality of cochain maps. -/
abbrev reindex {f' : K ⟶ L} (e : f = f') (m : Map f I J) : Map f' I J :=
  Plus.TermsIn.QuasiIsoTo.Map.reindex e m

/-- Reindexing an injective-resolution map retains its model morphism. -/
@[simp]
theorem reindex_modelHom {f' : K ⟶ L} (e : f = f') (m : Map f I J) :
    (reindex e m).modelHom = m.modelHom := sorry

/-- Reindexing an injective-resolution map retains its underlying cochain map. -/
@[simp]
theorem reindex_hom {f' : K ⟶ L} (e : f = f') (m : Map f I J) :
    (reindex e m).hom = m.hom := sorry

/-- Reindexing along reflexivity leaves an injective-resolution map unchanged. -/
@[simp]
theorem reindex_rfl (m : Map f I J) : reindex rfl m = m := sorry

/-- Successive reindexings of an injective-resolution map combine by transitivity. -/
@[simp]
theorem reindex_trans {f' f'' : K ⟶ L} (e : f = f') (e' : f' = f'')
    (m : Map f I J) :
    reindex e' (reindex e m) = reindex (e.trans e') m := sorry

/-- Reindexing along an equality and then its inverse recovers the injective-resolution map. -/
@[simp]
theorem reindex_symm {f' : K ⟶ L} (e : f = f') (m : Map f I J) :
    reindex e.symm (reindex e m) = m := sorry

/-- Reindexing the left cochain map of a composite agrees with reindexing its left factor. -/
@[simp]
theorem reindex_comp_left {f' : K ⟶ L} (e : f = f')
    (m : Map f I J) (n : Map g J H) :
    reindex (congrArg (fun k : K ⟶ L => k ≫ g) e) (comp m n) =
      comp (reindex e m) n := sorry

/-- Reindexing the right cochain map of a composite agrees with reindexing its right factor. -/
@[simp]
theorem reindex_comp_right {g' : L ⟶ M} (e : g = g')
    (m : Map f I J) (n : Map g J H) :
    reindex (congrArg (fun k : L ⟶ M => f ≫ k) e) (comp m n) =
      comp m (reindex e n) := sorry

/-- Reindexing both cochain maps of a composite commutes with composition. -/
@[simp]
theorem reindex_comp {f' : K ⟶ L} {g' : L ⟶ M}
    (e : f = f') (e' : g = g') (m : Map f I J) (n : Map g J H) :
    reindex (congrArg₂ (fun (a : K ⟶ L) (b : L ⟶ M) => a ≫ b) e e')
        (comp m n) =
      comp (reindex e m) (reindex e' n) := sorry

/-- Regard a morphism in one injective-resolution fiber as a map over the identity. -/
abbrev ofHom {I J : InjectiveResolution K} (m : I ⟶ J) : Map (𝟙 K) I J :=
  Plus.TermsIn.QuasiIsoTo.Map.ofHom m

/-- `ofHom` retains the morphism between injective models. -/
@[simp]
theorem ofHom_modelHom {I J : InjectiveResolution K} (m : I ⟶ J) :
    (ofHom m).modelHom = InjectiveResolution.modelHom m := sorry

/-- `ofHom` retains the underlying cochain map between injective models. -/
@[simp]
theorem ofHom_hom {I J : InjectiveResolution K} (m : I ⟶ J) :
    (ofHom m).hom = InjectiveResolution.hom m := sorry

/-- Regard an injective-resolution map over the identity as a morphism in one fiber. -/
abbrev toHom {I J : InjectiveResolution K} (m : Map (𝟙 K) I J) : I ⟶ J :=
  Plus.TermsIn.QuasiIsoTo.Map.toHom m

/-- `toHom` retains the morphism between injective models. -/
@[simp]
theorem toHom_modelHom {I J : InjectiveResolution K} (m : Map (𝟙 K) I J) :
    InjectiveResolution.modelHom (toHom m) = m.modelHom := sorry

/-- `toHom` retains the underlying cochain map between injective models. -/
@[simp]
theorem toHom_hom {I J : InjectiveResolution K} (m : Map (𝟙 K) I J) :
    InjectiveResolution.hom (toHom m) = m.hom := sorry

/-- Passing an injective-resolution morphism through `ofHom` and `toHom` returns it. -/
@[simp]
theorem toHom_ofHom {I J : InjectiveResolution K} (m : I ⟶ J) :
    toHom (ofHom m) = m := sorry

/-- Passing a map over the identity through `toHom` and `ofHom` returns it. -/
@[simp]
theorem ofHom_toHom {I J : InjectiveResolution K} (m : Map (𝟙 K) I J) :
    ofHom (toHom m) = m := sorry

/-- Morphisms in one injective-resolution fiber are equivalent to maps over the identity. -/
abbrev homEquiv {I J : InjectiveResolution K} : (I ⟶ J) ≃ Map (𝟙 K) I J :=
  Plus.TermsIn.QuasiIsoTo.Map.homEquiv

/-- `ofHom` sends an identity morphism in an injective-resolution fiber to the identity
resolution map. -/
@[simp]
theorem ofHom_id (I : InjectiveResolution K) :
    ofHom (𝟙 I) = id I := sorry

/-- `ofHom` sends composition in an injective-resolution fiber to composition of resolution
maps, after reindexing the composite identity map. -/
@[simp]
theorem ofHom_comp {I J H : InjectiveResolution K} (m : I ⟶ J) (n : J ⟶ H) :
    reindex (Category.id_comp (𝟙 K)) (comp (ofHom m) (ofHom n)) =
      ofHom (m ≫ n) := sorry

/-- `toHom` sends the identity resolution map to the identity morphism in its fiber. -/
@[simp]
theorem toHom_id (I : InjectiveResolution K) :
    toHom (id I) = 𝟙 I := sorry

/-- `toHom` sends composition of maps over the identity to composition in the
injective-resolution fiber, after reindexing the composite identity map. -/
@[simp]
theorem toHom_comp {I J H : InjectiveResolution K}
    (m : Map (𝟙 K) I J) (n : Map (𝟙 K) J H) :
    toHom (reindex (Category.id_comp (𝟙 K)) (comp m n)) =
      toHom m ≫ toHom n := sorry

/-- The left identity law for composition of injective-resolution maps. -/
@[simp]
theorem id_comp (m : Map f I J) :
    reindex (Category.id_comp f) (comp (id I) m) = m := sorry

/-- The right identity law for composition of injective-resolution maps. -/
@[simp]
theorem comp_id (m : Map f I J) :
    reindex (Category.comp_id f) (comp m (id J)) = m := sorry

/-- Composition of injective-resolution maps is associative after reindexing the cochain map. -/
theorem assoc (m : Map f I J) (n : Map g J H) (k : Map h H T) :
    reindex (Category.assoc f g h) (comp (comp m n) k) = comp m (comp n k) := sorry

end Map


end CochainComplex.InjectiveResolution


