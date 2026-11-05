module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Right.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps of Fixed-Lower-Bound Resolutions

This file gives cochain-complex names to the neutral maps between fixed-lower-bound right
resolutions. The data and its dependent composition remain owned by
`LocalizerMorphism.RightResolution.Map`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]
  {P : ObjectProperty A} {a : ℤ}

/-- A map of fixed-lower-bound termwise right resolutions over a cochain map. -/
@[stacks 05T6 "map of fixed-lower-bound resolutions"]
abbrev Map {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (R : QuasiIsoTo P a K) (S : QuasiIsoTo P a L) :=
  LocalizerMorphism.RightResolution.Map f R S

namespace Map

variable {K L M : CochainComplex A ℤ} {f : K ⟶ L} {g : L ⟶ M}
  {R : QuasiIsoTo P a K} {S : QuasiIsoTo P a L} {T : QuasiIsoTo P a M}

/-- The bundled fixed-bound model morphism underlying a resolution map. -/
abbrev modelHom (m : Map f R S) : R.model ⟶ S.model :=
  LocalizerMorphism.RightResolution.Map.modelHom m

/-- The cochain map between the underlying fixed-bound resolving complexes. -/
abbrev hom (m : Map f R S) : R.complex ⟶ S.complex :=
  LocalizerMorphism.RightResolution.Map.hom m

/-- A map of fixed-lower-bound resolutions commutes with the comparison maps. -/
@[reassoc]
theorem comparison_naturality (m : Map f R S) :
    R.comparison ≫ m.hom = f ≫ S.comparison := sorry

/-- Construct a fixed-lower-bound resolution map from a bundled model morphism and its
comparison square. -/
def mk (modelHom : R.model ⟶ S.model)
    (naturality : R.comparison ≫ (StrictlyGE.TermsIn.ι P a).map modelHom =
      f ≫ S.comparison) : Map f R S where
  modelHom := modelHom
  comparison_naturality := naturality

/-- The fixed-bound constructor retains the supplied model morphism. -/
@[simp]
theorem mk_modelHom (modelHom : R.model ⟶ S.model)
    (naturality : R.comparison ≫ (StrictlyGE.TermsIn.ι P a).map modelHom =
      f ≫ S.comparison) :
    (mk modelHom naturality).modelHom = modelHom := sorry

/-- The cochain map of the fixed-bound constructor is induced by the inclusion functor. -/
@[simp]
theorem mk_hom (modelHom : R.model ⟶ S.model)
    (naturality : R.comparison ≫ (StrictlyGE.TermsIn.ι P a).map modelHom =
      f ≫ S.comparison) :
    (mk modelHom naturality).hom = (StrictlyGE.TermsIn.ι P a).map modelHom := sorry

/-- Maps of fixed-lower-bound resolutions are determined by their model morphisms. -/
@[ext]
theorem ext {m n : Map f R S} (h : m.modelHom = n.modelHom) : m = n := sorry

/-- The identity map of a fixed-lower-bound resolution. -/
abbrev id (R : QuasiIsoTo P a K) : Map (𝟙 K) R R :=
  LocalizerMorphism.RightResolution.Map.id R

/-- Compose maps of fixed-lower-bound resolutions. -/
abbrev comp (m : Map f R S) (n : Map g S T) : Map (f ≫ g) R T :=
  LocalizerMorphism.RightResolution.Map.comp m n

/-- Reindex a fixed-lower-bound resolution map along an equality of base cochain maps. -/
abbrev reindex {f' : K ⟶ L} (e : f = f') (m : Map f R S) : Map f' R S :=
  LocalizerMorphism.RightResolution.Map.reindex e m

/-- Regard a morphism in one fixed-bound resolution fiber as a map over the identity. -/
abbrev ofHom {R S : QuasiIsoTo P a K} (m : R ⟶ S) : Map (𝟙 K) R S :=
  LocalizerMorphism.RightResolution.Map.ofHom m

/-- Regard a fixed-bound resolution map over the identity as a morphism in one fiber. -/
abbrev toHom {R S : QuasiIsoTo P a K} (m : Map (𝟙 K) R S) : R ⟶ S :=
  LocalizerMorphism.RightResolution.Map.toHom m

/-- Morphisms in one fixed-bound resolution fiber are equivalent to maps over the identity. -/
abbrev homEquiv {R S : QuasiIsoTo P a K} : (R ⟶ S) ≃ Map (𝟙 K) R S :=
  LocalizerMorphism.RightResolution.Map.homEquiv

end Map

end CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo


