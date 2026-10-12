/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Variable
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Left.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps of Variable-Upper-Bound Left Resolutions

This leaf gives cochain-complex names to the generic maps between bounded-above termwise left
resolutions over different source complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.Minus.TermsIn.QuasiIsoFrom

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]
  {P : ObjectProperty A}

/-- A map of variable-upper-bound termwise left resolutions over a cochain map. -/
@[stacks 05T7 "map of variable-upper-bound resolutions"]
abbrev Map {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (R : QuasiIsoFrom P K) (S : QuasiIsoFrom P L) :=
  LocalizerMorphism.LeftResolution.Map f R S

namespace Map

variable {K L M : CochainComplex A ℤ} {f : K ⟶ L} {g : L ⟶ M}
  {R : QuasiIsoFrom P K} {S : QuasiIsoFrom P L} {T : QuasiIsoFrom P M}

variable {N : CochainComplex A ℤ} {h : M ⟶ N} {U : QuasiIsoFrom P N}

/-- The bundled termwise model morphism underlying a map of left resolutions. -/
abbrev modelHom (m : Map f R S) : R.model ⟶ S.model :=
  LocalizerMorphism.LeftResolution.Map.modelHom m

/-- The cochain map between the resolving complexes. -/
abbrev hom (m : Map f R S) : R.complex ⟶ S.complex :=
  LocalizerMorphism.LeftResolution.Map.hom m

/-- A map of variable-upper-bound left resolutions commutes with the comparison maps. -/
@[reassoc]
theorem comparison_naturality (m : Map f R S) :
    m.hom ≫ S.comparison = R.comparison ≫ f := sorry

/-- Construct a map of variable-upper-bound left resolutions from its model morphism and
comparison square. -/
def mk (modelHom : R.model ⟶ S.model)
    (naturality : (Minus.TermsIn.ι P).map modelHom ≫ S.comparison = R.comparison ≫ f) :
    Map f R S where
  modelHom := modelHom
  comparison_naturality := naturality

/-- The named constructor retains the supplied morphism between termwise models. -/
@[simp]
theorem mk_modelHom (modelHom : R.model ⟶ S.model)
    (naturality : (Minus.TermsIn.ι P).map modelHom ≫ S.comparison = R.comparison ≫ f) :
    (mk modelHom naturality).modelHom = modelHom := sorry

/-- The cochain map of the named constructor is induced by the inclusion functor. -/
@[simp]
theorem mk_hom (modelHom : R.model ⟶ S.model)
    (naturality : (Minus.TermsIn.ι P).map modelHom ≫ S.comparison = R.comparison ≫ f) :
    (mk modelHom naturality).hom = (Minus.TermsIn.ι P).map modelHom := sorry

/-- Maps of variable-upper-bound left resolutions are determined by their model morphisms. -/
@[ext]
theorem ext {m n : Map f R S} (h : m.modelHom = n.modelHom) : m = n := sorry

/-- The identity map of a variable-upper-bound left resolution. -/
abbrev id (R : QuasiIsoFrom P K) : Map (𝟙 K) R R :=
  LocalizerMorphism.LeftResolution.Map.id R

/-- The identity resolution map has identity model morphism. -/
@[simp]
theorem id_modelHom (R : QuasiIsoFrom P K) : (id R).modelHom = 𝟙 R.model := sorry

/-- The identity resolution map has identity underlying cochain map. -/
@[simp]
theorem id_hom (R : QuasiIsoFrom P K) : (id R).hom = 𝟙 R.complex := sorry

/-- Compose maps of variable-upper-bound left resolutions. -/
abbrev comp (m : Map f R S) (n : Map g S T) : Map (f ≫ g) R T :=
  LocalizerMorphism.LeftResolution.Map.comp m n

/-- Composition of resolution maps composes their model morphisms. -/
@[simp]
theorem comp_modelHom (m : Map f R S) (n : Map g S T) :
    (comp m n).modelHom = m.modelHom ≫ n.modelHom := sorry

/-- Composition of resolution maps composes their underlying cochain maps. -/
@[simp]
theorem comp_hom (m : Map f R S) (n : Map g S T) :
    (comp m n).hom = m.hom ≫ n.hom := sorry

/-- Reindex a map of left resolutions along an equality of cochain maps. -/
abbrev reindex {f' : K ⟶ L} (e : f = f') (m : Map f R S) : Map f' R S :=
  LocalizerMorphism.LeftResolution.Map.reindex e m

/-- Reindexing a resolution map retains its model morphism. -/
@[simp]
theorem reindex_modelHom {f' : K ⟶ L} (e : f = f') (m : Map f R S) :
    (reindex e m).modelHom = m.modelHom := sorry

/-- Reindexing a resolution map retains its underlying cochain map. -/
@[simp]
theorem reindex_hom {f' : K ⟶ L} (e : f = f') (m : Map f R S) :
    (reindex e m).hom = m.hom := sorry

/-- Reindexing along reflexivity leaves a variable-upper-bound resolution map unchanged. -/
@[simp]
theorem reindex_rfl (m : Map f R S) : reindex rfl m = m := sorry

/-- Successive reindexings of a variable-upper-bound resolution map combine by transitivity. -/
@[simp]
theorem reindex_trans {f' f'' : K ⟶ L} (e : f = f') (e' : f' = f'')
    (m : Map f R S) :
    reindex e' (reindex e m) = reindex (e.trans e') m := sorry

/-- Reindexing along an equality and then its inverse recovers the original
variable-upper-bound resolution map. -/
@[simp]
theorem reindex_symm {f' : K ⟶ L} (e : f = f') (m : Map f R S) :
    reindex e.symm (reindex e m) = m := sorry

/-- Reindexing the left cochain map of a composite agrees with reindexing its left factor. -/
@[simp]
theorem reindex_comp_left {f' : K ⟶ L} (e : f = f')
    (m : Map f R S) (n : Map g S T) :
    reindex (congrArg (fun k : K ⟶ L => k ≫ g) e) (comp m n) =
      comp (reindex e m) n := sorry

/-- Reindexing the right cochain map of a composite agrees with reindexing its right factor. -/
@[simp]
theorem reindex_comp_right {g' : L ⟶ M} (e : g = g')
    (m : Map f R S) (n : Map g S T) :
    reindex (congrArg (fun k : L ⟶ M => f ≫ k) e) (comp m n) =
      comp m (reindex e n) := sorry

/-- Reindexing both cochain maps of a composite commutes with composition. -/
@[simp]
theorem reindex_comp {f' : K ⟶ L} {g' : L ⟶ M}
    (e : f = f') (e' : g = g') (m : Map f R S) (n : Map g S T) :
    reindex (congrArg₂ (fun (a : K ⟶ L) (b : L ⟶ M) => a ≫ b) e e')
        (comp m n) =
      comp (reindex e m) (reindex e' n) := sorry

/-- Regard a morphism in one resolution fiber as a map over the identity cochain map. -/
abbrev ofHom {R S : QuasiIsoFrom P K} (m : R ⟶ S) : Map (𝟙 K) R S :=
  LocalizerMorphism.LeftResolution.Map.ofHom m

/-- `ofHom` retains the morphism between bundled bounded-above models. -/
@[simp]
theorem ofHom_modelHom {R S : QuasiIsoFrom P K} (m : R ⟶ S) :
    (ofHom m).modelHom = QuasiIsoFrom.modelHom m := sorry

/-- `ofHom` retains the underlying cochain map between bounded-above models. -/
@[simp]
theorem ofHom_hom {R S : QuasiIsoFrom P K} (m : R ⟶ S) :
    (ofHom m).hom = QuasiIsoFrom.hom m := sorry

/-- Sending an identity fiber morphism through `ofHom` gives the identity resolution map. -/
@[simp]
theorem ofHom_id (R : QuasiIsoFrom P K) :
    ofHom (𝟙 R) = id R := sorry

/-- Sending a composite fiber morphism through `ofHom` gives the composite resolution map after
reindexing its base identity. -/
@[simp]
theorem ofHom_comp {R S T : QuasiIsoFrom P K} (m : R ⟶ S) (n : S ⟶ T) :
    reindex (Category.id_comp (𝟙 K)) (comp (ofHom m) (ofHom n)) =
      ofHom (m ≫ n) := sorry

/-- Regard a resolution map over the identity as a morphism in one resolution fiber. -/
abbrev toHom {R S : QuasiIsoFrom P K} (m : Map (𝟙 K) R S) : R ⟶ S :=
  LocalizerMorphism.LeftResolution.Map.toHom m

/-- `toHom` retains the morphism between bundled bounded-above models. -/
@[simp]
theorem toHom_modelHom {R S : QuasiIsoFrom P K} (m : Map (𝟙 K) R S) :
    QuasiIsoFrom.modelHom (toHom m) = m.modelHom := sorry

/-- `toHom` retains the underlying cochain map between bounded-above models. -/
@[simp]
theorem toHom_hom {R S : QuasiIsoFrom P K} (m : Map (𝟙 K) R S) :
    QuasiIsoFrom.hom (toHom m) = m.hom := sorry

/-- Sending the identity resolution map through `toHom` gives the identity fiber morphism. -/
@[simp]
theorem toHom_id (R : QuasiIsoFrom P K) :
    toHom (id R) = 𝟙 R := sorry

/-- Sending a composite of maps over the identity through `toHom` gives the composite fiber
morphism after reindexing the base map. -/
@[simp]
theorem toHom_comp {R S T : QuasiIsoFrom P K}
    (m : Map (𝟙 K) R S) (n : Map (𝟙 K) S T) :
    toHom (reindex (Category.id_comp (𝟙 K)) (comp m n)) = toHom m ≫ toHom n := sorry

/-- Passing a variable-upper-bound resolution morphism through `ofHom` and `toHom` returns it. -/
@[simp]
theorem toHom_ofHom {R S : QuasiIsoFrom P K} (m : R ⟶ S) :
    toHom (ofHom m) = m := sorry

/-- Passing a map over the identity through `toHom` and `ofHom` returns it. -/
@[simp]
theorem ofHom_toHom {R S : QuasiIsoFrom P K} (m : Map (𝟙 K) R S) :
    ofHom (toHom m) = m := sorry

/-- Morphisms in one resolution fiber are equivalent to maps over the identity cochain map. -/
abbrev homEquiv {R S : QuasiIsoFrom P K} : (R ⟶ S) ≃ Map (𝟙 K) R S :=
  LocalizerMorphism.LeftResolution.Map.homEquiv

/-- The left identity law for composition of variable-upper-bound left-resolution maps. -/
@[simp]
theorem id_comp (m : Map f R S) :
    reindex (Category.id_comp f) (comp (id R) m) = m := sorry

/-- The right identity law for composition of variable-upper-bound left-resolution maps. -/
@[simp]
theorem comp_id (m : Map f R S) :
    reindex (Category.comp_id f) (comp m (id S)) = m := sorry

/-- Composition of variable-upper-bound left-resolution maps is associative after reindexing. -/
theorem assoc (m : Map f R S) (n : Map g S T) (k : Map h T U) :
    reindex (Category.assoc f g h) (comp (comp m n) k) = comp m (comp n k) := sorry

end Map

end CochainComplex.Minus.TermsIn.QuasiIsoFrom


