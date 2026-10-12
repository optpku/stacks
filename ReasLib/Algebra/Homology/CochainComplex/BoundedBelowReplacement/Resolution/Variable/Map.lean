/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Variable
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Right.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps of Variable-Lower-Bound Right Resolutions

This leaf gives cochain-complex names to the generic maps between bounded-below termwise right
resolutions over different source complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.Plus.TermsIn.QuasiIsoTo

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]
  {P : ObjectProperty A}

/-- A map of variable-lower-bound termwise right resolutions over a cochain map. -/
@[stacks 05T6 "map of variable-lower-bound resolutions"]
abbrev Map {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (R : QuasiIsoTo P K) (S : QuasiIsoTo P L) :=
  LocalizerMorphism.RightResolution.Map f R S

namespace Map

variable {K L M : CochainComplex A ℤ} {f : K ⟶ L} {g : L ⟶ M}
  {R : QuasiIsoTo P K} {S : QuasiIsoTo P L} {T : QuasiIsoTo P M}

variable {N : CochainComplex A ℤ} {h : M ⟶ N} {U : QuasiIsoTo P N}

/-- The bundled termwise model morphism underlying a map of right resolutions. -/
abbrev modelHom (m : Map f R S) : R.model ⟶ S.model :=
  LocalizerMorphism.RightResolution.Map.modelHom m

/-- The cochain map between the resolving complexes. -/
abbrev hom (m : Map f R S) : R.complex ⟶ S.complex :=
  LocalizerMorphism.RightResolution.Map.hom m

/-- A map of variable-lower-bound right resolutions commutes with the comparison maps. -/
@[reassoc]
theorem comparison_naturality (m : Map f R S) :
    R.comparison ≫ m.hom = f ≫ S.comparison := sorry

/-- Construct a map of variable-lower-bound right resolutions from its model morphism and
comparison square. -/
def mk (modelHom : R.model ⟶ S.model)
    (naturality : R.comparison ≫ (Plus.TermsIn.ι P).map modelHom = f ≫ S.comparison) :
    Map f R S where
  modelHom := modelHom
  comparison_naturality := naturality

/-- The named constructor retains the supplied morphism between termwise models. -/
@[simp]
theorem mk_modelHom (modelHom : R.model ⟶ S.model)
    (naturality : R.comparison ≫ (Plus.TermsIn.ι P).map modelHom = f ≫ S.comparison) :
    (mk modelHom naturality).modelHom = modelHom := sorry

/-- The cochain map of the named constructor is induced by the inclusion functor. -/
@[simp]
theorem mk_hom (modelHom : R.model ⟶ S.model)
    (naturality : R.comparison ≫ (Plus.TermsIn.ι P).map modelHom = f ≫ S.comparison) :
    (mk modelHom naturality).hom = (Plus.TermsIn.ι P).map modelHom := sorry

/-- Maps of variable-lower-bound right resolutions are determined by their model morphisms. -/
@[ext]
theorem ext {m n : Map f R S} (h : m.modelHom = n.modelHom) : m = n := sorry

/-- The identity map of a variable-lower-bound right resolution. -/
abbrev id (R : QuasiIsoTo P K) : Map (𝟙 K) R R :=
  LocalizerMorphism.RightResolution.Map.id R

/-- The identity resolution map has identity model morphism. -/
@[simp]
theorem id_modelHom (R : QuasiIsoTo P K) : (id R).modelHom = 𝟙 R.model := sorry

/-- The identity resolution map has identity underlying cochain map. -/
@[simp]
theorem id_hom (R : QuasiIsoTo P K) : (id R).hom = 𝟙 R.complex := sorry

/-- Compose maps of variable-lower-bound right resolutions. -/
abbrev comp (m : Map f R S) (n : Map g S T) : Map (f ≫ g) R T :=
  LocalizerMorphism.RightResolution.Map.comp m n

/-- Composition of resolution maps composes their model morphisms. -/
@[simp]
theorem comp_modelHom (m : Map f R S) (n : Map g S T) :
    (comp m n).modelHom = m.modelHom ≫ n.modelHom := sorry

/-- Composition of resolution maps composes their underlying cochain maps. -/
@[simp]
theorem comp_hom (m : Map f R S) (n : Map g S T) :
    (comp m n).hom = m.hom ≫ n.hom := sorry

/-- Reindex a map of right resolutions along an equality of cochain maps. -/
abbrev reindex {f' : K ⟶ L} (e : f = f') (m : Map f R S) : Map f' R S :=
  LocalizerMorphism.RightResolution.Map.reindex e m

/-- Reindexing a resolution map retains its model morphism. -/
@[simp]
theorem reindex_modelHom {f' : K ⟶ L} (e : f = f') (m : Map f R S) :
    (reindex e m).modelHom = m.modelHom := sorry

/-- Reindexing a resolution map retains its underlying cochain map. -/
@[simp]
theorem reindex_hom {f' : K ⟶ L} (e : f = f') (m : Map f R S) :
    (reindex e m).hom = m.hom := sorry

/-- Reindexing along reflexivity leaves a variable-lower-bound resolution map unchanged. -/
@[simp]
theorem reindex_rfl (m : Map f R S) : reindex rfl m = m := sorry

/-- Successive reindexings of a variable-lower-bound resolution map combine by transitivity. -/
@[simp]
theorem reindex_trans {f' f'' : K ⟶ L} (e : f = f') (e' : f' = f'')
    (m : Map f R S) :
    reindex e' (reindex e m) = reindex (e.trans e') m := sorry

/-- Reindexing along an equality and then its inverse recovers the original
variable-lower-bound resolution map. -/
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
abbrev ofHom {R S : QuasiIsoTo P K} (m : R ⟶ S) : Map (𝟙 K) R S :=
  LocalizerMorphism.RightResolution.Map.ofHom m

/-- `ofHom` retains the morphism between bundled bounded-below models. -/
@[simp]
theorem ofHom_modelHom {R S : QuasiIsoTo P K} (m : R ⟶ S) :
    (ofHom m).modelHom = QuasiIsoTo.modelHom m := sorry

/-- `ofHom` retains the underlying cochain map between bounded-below models. -/
@[simp]
theorem ofHom_hom {R S : QuasiIsoTo P K} (m : R ⟶ S) :
    (ofHom m).hom = QuasiIsoTo.hom m := sorry

/-- Sending an identity fiber morphism through `ofHom` gives the identity resolution map. -/
@[simp]
theorem ofHom_id (R : QuasiIsoTo P K) :
    ofHom (𝟙 R) = id R := sorry

/-- Sending a composite fiber morphism through `ofHom` gives the composite resolution map after
reindexing its base identity. -/
@[simp]
theorem ofHom_comp {R S T : QuasiIsoTo P K} (m : R ⟶ S) (n : S ⟶ T) :
    reindex (Category.id_comp (𝟙 K)) (comp (ofHom m) (ofHom n)) =
      ofHom (m ≫ n) := sorry

/-- Regard a resolution map over the identity as a morphism in one resolution fiber. -/
abbrev toHom {R S : QuasiIsoTo P K} (m : Map (𝟙 K) R S) : R ⟶ S :=
  LocalizerMorphism.RightResolution.Map.toHom m

/-- `toHom` retains the morphism between bundled bounded-below models. -/
@[simp]
theorem toHom_modelHom {R S : QuasiIsoTo P K} (m : Map (𝟙 K) R S) :
    QuasiIsoTo.modelHom (toHom m) = m.modelHom := sorry

/-- `toHom` retains the underlying cochain map between bounded-below models. -/
@[simp]
theorem toHom_hom {R S : QuasiIsoTo P K} (m : Map (𝟙 K) R S) :
    QuasiIsoTo.hom (toHom m) = m.hom := sorry

/-- Sending the identity resolution map through `toHom` gives the identity fiber morphism. -/
@[simp]
theorem toHom_id (R : QuasiIsoTo P K) :
    toHom (id R) = 𝟙 R := sorry

/-- Sending a composite of maps over the identity through `toHom` gives the composite fiber
morphism after reindexing the base map. -/
@[simp]
theorem toHom_comp {R S T : QuasiIsoTo P K}
    (m : Map (𝟙 K) R S) (n : Map (𝟙 K) S T) :
    toHom (reindex (Category.id_comp (𝟙 K)) (comp m n)) = toHom m ≫ toHom n := sorry

/-- Passing a variable-lower-bound resolution morphism through `ofHom` and `toHom` returns it. -/
@[simp]
theorem toHom_ofHom {R S : QuasiIsoTo P K} (m : R ⟶ S) :
    toHom (ofHom m) = m := sorry

/-- Passing a map over the identity through `toHom` and `ofHom` returns it. -/
@[simp]
theorem ofHom_toHom {R S : QuasiIsoTo P K} (m : Map (𝟙 K) R S) :
    ofHom (toHom m) = m := sorry

/-- Morphisms in one resolution fiber are equivalent to maps over the identity cochain map. -/
abbrev homEquiv {R S : QuasiIsoTo P K} : (R ⟶ S) ≃ Map (𝟙 K) R S :=
  LocalizerMorphism.RightResolution.Map.homEquiv

/-- The left identity law for composition of variable-lower-bound right-resolution maps. -/
@[simp]
theorem id_comp (m : Map f R S) :
    reindex (Category.id_comp f) (comp (id R) m) = m := sorry

/-- The right identity law for composition of variable-lower-bound right-resolution maps. -/
@[simp]
theorem comp_id (m : Map f R S) :
    reindex (Category.comp_id f) (comp m (id S)) = m := sorry

/-- Composition of variable-lower-bound right-resolution maps is associative after reindexing. -/
theorem assoc (m : Map f R S) (n : Map g S T) (k : Map h T U) :
    reindex (Category.assoc f g h) (comp (comp m n) k) = comp m (comp n k) := sorry

end Map

end CochainComplex.Plus.TermsIn.QuasiIsoTo


