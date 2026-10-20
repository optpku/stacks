/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution.Basic
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Variable.Map

/-!
# Maps of Projective Resolutions

This file specializes the neutral cross-object left-resolution map to bounded-above projective
models.  It packages the comparison square used by downstream derived and Ext constructions.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex.ProjectiveResolution

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- A map of projective resolutions lying over a cochain map. -/
@[stacks 0643 "map of projective resolutions"]
abbrev Map {K L : CochainComplex 𝒜 ℤ} (f : K ⟶ L)
    (P : ProjectiveResolution K) (Q : ProjectiveResolution L) :=
  Minus.TermsIn.QuasiIsoFrom.Map f P Q

namespace Map

variable {K L M : CochainComplex 𝒜 ℤ} {f : K ⟶ L} {g : L ⟶ M}
  {P : ProjectiveResolution K} {Q : ProjectiveResolution L}
  {R : ProjectiveResolution M}

variable {N : CochainComplex 𝒜 ℤ} {h : M ⟶ N} {T : ProjectiveResolution N}

/-- The morphism between bounded-above projective models. -/
abbrev modelHom (m : Map f P Q) : P.model ⟶ Q.model :=
  Minus.TermsIn.QuasiIsoFrom.Map.modelHom m

/-- The cochain map between the resolving complexes. -/
abbrev hom (m : Map f P Q) : P.complex ⟶ Q.complex :=
  Minus.TermsIn.QuasiIsoFrom.Map.hom m

/-- Construct a map of projective resolutions from its morphism of projective models and
comparison square. -/
def mk (modelHom : P.model ⟶ Q.model)
    (naturality : (ProjectiveMinus.ι 𝒜).map modelHom ≫ Q.π = P.π ≫ f) : Map f P Q :=
  Minus.TermsIn.QuasiIsoFrom.Map.mk modelHom naturality

/-- The named constructor retains the supplied morphism between projective models. -/
@[simp]
theorem mk_modelHom (modelHom : P.model ⟶ Q.model)
    (naturality : (ProjectiveMinus.ι 𝒜).map modelHom ≫ Q.π = P.π ≫ f) :
    (mk modelHom naturality).modelHom = modelHom := sorry

/-- The cochain map of the named constructor is induced by the projective-model inclusion. -/
@[simp]
theorem mk_hom (modelHom : P.model ⟶ Q.model)
    (naturality : (ProjectiveMinus.ι 𝒜).map modelHom ≫ Q.π = P.π ≫ f) :
    (mk modelHom naturality).hom = (ProjectiveMinus.ι 𝒜).map modelHom := sorry

/-- Maps of projective resolutions are determined by their morphisms of projective models. -/
@[ext]
theorem ext {m n : Map f P Q} (h : m.modelHom = n.modelHom) : m = n := sorry

/-- A map of projective resolutions commutes with the comparison maps. -/
@[reassoc]
theorem π_naturality (m : Map f P Q) : m.hom ≫ Q.π = P.π ≫ f := sorry

/-- The identity map of a projective resolution. -/
abbrev id (P : ProjectiveResolution K) : Map (𝟙 K) P P :=
  Minus.TermsIn.QuasiIsoFrom.Map.id P

/-- The identity projective-resolution map has identity model morphism. -/
@[simp]
theorem id_modelHom (P : ProjectiveResolution K) : (id P).modelHom = 𝟙 P.model := sorry

/-- The identity projective-resolution map has identity underlying cochain map. -/
@[simp]
theorem id_hom (P : ProjectiveResolution K) : (id P).hom = 𝟙 P.complex := sorry

/-- Compose maps of projective resolutions. -/
abbrev comp (m : Map f P Q) (n : Map g Q R) : Map (f ≫ g) P R :=
  Minus.TermsIn.QuasiIsoFrom.Map.comp m n

/-- Composition of projective-resolution maps composes their model morphisms. -/
@[simp]
theorem comp_modelHom (m : Map f P Q) (n : Map g Q R) :
    (comp m n).modelHom = m.modelHom ≫ n.modelHom := sorry

/-- Composition of projective-resolution maps composes their underlying cochain maps. -/
@[simp]
theorem comp_hom (m : Map f P Q) (n : Map g Q R) :
    (comp m n).hom = m.hom ≫ n.hom := sorry

/-- Reindex a map of projective resolutions along an equality of cochain maps. -/
abbrev reindex {f' : K ⟶ L} (e : f = f') (m : Map f P Q) : Map f' P Q :=
  Minus.TermsIn.QuasiIsoFrom.Map.reindex e m

/-- Reindexing a projective-resolution map retains its model morphism. -/
@[simp]
theorem reindex_modelHom {f' : K ⟶ L} (e : f = f') (m : Map f P Q) :
    (reindex e m).modelHom = m.modelHom := sorry

/-- Reindexing a projective-resolution map retains its underlying cochain map. -/
@[simp]
theorem reindex_hom {f' : K ⟶ L} (e : f = f') (m : Map f P Q) :
    (reindex e m).hom = m.hom := sorry

/-- Reindexing along reflexivity leaves a projective-resolution map unchanged. -/
@[simp]
theorem reindex_rfl (m : Map f P Q) : reindex rfl m = m := sorry

/-- Successive reindexings of a projective-resolution map combine by transitivity. -/
@[simp]
theorem reindex_trans {f' f'' : K ⟶ L} (e : f = f') (e' : f' = f'')
    (m : Map f P Q) :
    reindex e' (reindex e m) = reindex (e.trans e') m := sorry

/-- Reindexing along an equality and then its inverse recovers the projective-resolution map. -/
@[simp]
theorem reindex_symm {f' : K ⟶ L} (e : f = f') (m : Map f P Q) :
    reindex e.symm (reindex e m) = m := sorry

/-- Reindexing the left cochain map of a composite agrees with reindexing its left factor. -/
@[simp]
theorem reindex_comp_left {f' : K ⟶ L} (e : f = f')
    (m : Map f P Q) (n : Map g Q R) :
    reindex (congrArg (fun k : K ⟶ L => k ≫ g) e) (comp m n) =
      comp (reindex e m) n := sorry

/-- Reindexing the right cochain map of a composite agrees with reindexing its right factor. -/
@[simp]
theorem reindex_comp_right {g' : L ⟶ M} (e : g = g')
    (m : Map f P Q) (n : Map g Q R) :
    reindex (congrArg (fun k : L ⟶ M => f ≫ k) e) (comp m n) =
      comp m (reindex e n) := sorry

/-- Reindexing both cochain maps of a composite commutes with composition. -/
@[simp]
theorem reindex_comp {f' : K ⟶ L} {g' : L ⟶ M}
    (e : f = f') (e' : g = g') (m : Map f P Q) (n : Map g Q R) :
    reindex (congrArg₂ (fun (a : K ⟶ L) (b : L ⟶ M) => a ≫ b) e e')
        (comp m n) =
      comp (reindex e m) (reindex e' n) := sorry

/-- Regard a morphism in one projective-resolution fiber as a map over the identity. -/
abbrev ofHom {P Q : ProjectiveResolution K} (m : P ⟶ Q) : Map (𝟙 K) P Q :=
  Minus.TermsIn.QuasiIsoFrom.Map.ofHom m

/-- `ofHom` retains the morphism between projective models. -/
@[simp]
theorem ofHom_modelHom {P Q : ProjectiveResolution K} (m : P ⟶ Q) :
    (ofHom m).modelHom = ProjectiveResolution.modelHom m := sorry

/-- `ofHom` retains the underlying cochain map between projective models. -/
@[simp]
theorem ofHom_hom {P Q : ProjectiveResolution K} (m : P ⟶ Q) :
    (ofHom m).hom = ProjectiveResolution.hom m := sorry

/-- Regard a projective-resolution map over the identity as a morphism in one fiber. -/
abbrev toHom {P Q : ProjectiveResolution K} (m : Map (𝟙 K) P Q) : P ⟶ Q :=
  Minus.TermsIn.QuasiIsoFrom.Map.toHom m

/-- `toHom` retains the morphism between projective models. -/
@[simp]
theorem toHom_modelHom {P Q : ProjectiveResolution K} (m : Map (𝟙 K) P Q) :
    ProjectiveResolution.modelHom (toHom m) = m.modelHom := sorry

/-- `toHom` retains the underlying cochain map between projective models. -/
@[simp]
theorem toHom_hom {P Q : ProjectiveResolution K} (m : Map (𝟙 K) P Q) :
    ProjectiveResolution.hom (toHom m) = m.hom := sorry

/-- Passing a projective-resolution morphism through `ofHom` and `toHom` returns it. -/
@[simp]
theorem toHom_ofHom {P Q : ProjectiveResolution K} (m : P ⟶ Q) :
    toHom (ofHom m) = m := sorry

/-- Passing a map over the identity through `toHom` and `ofHom` returns it. -/
@[simp]
theorem ofHom_toHom {P Q : ProjectiveResolution K} (m : Map (𝟙 K) P Q) :
    ofHom (toHom m) = m := sorry

/-- Morphisms in one projective-resolution fiber are equivalent to maps over the identity. -/
abbrev homEquiv {P Q : ProjectiveResolution K} : (P ⟶ Q) ≃ Map (𝟙 K) P Q :=
  Minus.TermsIn.QuasiIsoFrom.Map.homEquiv

/-- `ofHom` sends an identity morphism in a projective-resolution fiber to the identity
resolution map. -/
@[simp]
theorem ofHom_id (P : ProjectiveResolution K) :
    ofHom (𝟙 P) = id P := sorry

/-- `ofHom` sends composition in a projective-resolution fiber to composition of resolution
maps, after reindexing the composite identity map. -/
@[simp]
theorem ofHom_comp {P Q R : ProjectiveResolution K} (m : P ⟶ Q) (n : Q ⟶ R) :
    reindex (Category.id_comp (𝟙 K)) (comp (ofHom m) (ofHom n)) =
      ofHom (m ≫ n) := sorry

/-- `toHom` sends the identity resolution map to the identity morphism in its fiber. -/
@[simp]
theorem toHom_id (P : ProjectiveResolution K) :
    toHom (id P) = 𝟙 P := sorry

/-- `toHom` sends composition of maps over the identity to composition in the
projective-resolution fiber, after reindexing the composite identity map. -/
@[simp]
theorem toHom_comp {P Q R : ProjectiveResolution K}
    (m : Map (𝟙 K) P Q) (n : Map (𝟙 K) Q R) :
    toHom (reindex (Category.id_comp (𝟙 K)) (comp m n)) =
      toHom m ≫ toHom n := sorry

/-- The left identity law for composition of projective-resolution maps. -/
@[simp]
theorem id_comp (m : Map f P Q) :
    reindex (Category.id_comp f) (comp (id P) m) = m := sorry

/-- The right identity law for composition of projective-resolution maps. -/
@[simp]
theorem comp_id (m : Map f P Q) :
    reindex (Category.comp_id f) (comp m (id Q)) = m := sorry

/-- Composition of projective-resolution maps is associative after reindexing the cochain map. -/
theorem assoc (m : Map f P Q) (n : Map g Q R) (k : Map h R T) :
    reindex (Category.assoc f g h) (comp (comp m n) k) = comp m (comp n k) := sorry

end Map

end CochainComplex.ProjectiveResolution
