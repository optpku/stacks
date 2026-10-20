module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Left.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps of Fixed-Upper-Bound Left Resolutions

This file specializes maps of left resolutions to termwise models with a fixed upper bound.  The
construction and its operations remain owned by the neutral localizer-morphism API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]
  {P : ObjectProperty A} {a : ℤ}

/-- A map of fixed-upper-bound termwise left resolutions over a cochain map. -/
@[stacks 05T7 "map of fixed-upper-bound resolutions"]
abbrev Map {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (R : QuasiIsoFrom P a K) (S : QuasiIsoFrom P a L) :=
  LocalizerMorphism.LeftResolution.Map f R S

namespace Map

variable {K L M : CochainComplex A ℤ} {f : K ⟶ L} {g : L ⟶ M}
  {R : QuasiIsoFrom P a K} {S : QuasiIsoFrom P a L} {T : QuasiIsoFrom P a M}

/-- The bundled fixed-upper-bound model morphism underlying a resolution map. -/
abbrev modelHom (m : Map f R S) : R.model ⟶ S.model :=
  LocalizerMorphism.LeftResolution.Map.modelHom m

/-- The cochain map between the underlying fixed-upper-bound models. -/
abbrev hom (m : Map f R S) : R.complex ⟶ S.complex :=
  LocalizerMorphism.LeftResolution.Map.hom m

/-- A map of fixed-upper-bound left resolutions commutes with the comparison maps. -/
@[reassoc]
theorem comparison_naturality (m : Map f R S) :
    m.hom ≫ S.comparison = R.comparison ≫ f := sorry

/-- Construct a fixed-upper-bound resolution map from a model morphism and its comparison
square. -/
def mk (modelHom : R.model ⟶ S.model)
    (naturality : (StrictlyLE.TermsIn.ι P a).map modelHom ≫ S.comparison =
      R.comparison ≫ f) :
    Map f R S where
  modelHom := modelHom
  comparison_naturality := naturality

/-- The named constructor retains the supplied fixed-upper-bound model morphism. -/
@[simp]
theorem mk_modelHom (modelHom : R.model ⟶ S.model)
    (naturality : (StrictlyLE.TermsIn.ι P a).map modelHom ≫ S.comparison =
      R.comparison ≫ f) :
    (mk modelHom naturality).modelHom = modelHom := sorry

/-- The cochain map of the named constructor is induced by the fixed-bound inclusion. -/
@[simp]
theorem mk_hom (modelHom : R.model ⟶ S.model)
    (naturality : (StrictlyLE.TermsIn.ι P a).map modelHom ≫ S.comparison =
      R.comparison ≫ f) :
    (mk modelHom naturality).hom = (StrictlyLE.TermsIn.ι P a).map modelHom := sorry

/-- Maps of fixed-upper-bound left resolutions are determined by their model morphisms. -/
@[ext]
theorem ext {m n : Map f R S} (h : m.modelHom = n.modelHom) : m = n := sorry

/-- The identity map of a fixed-upper-bound left resolution. -/
abbrev id (R : QuasiIsoFrom P a K) : Map (𝟙 K) R R :=
  LocalizerMorphism.LeftResolution.Map.id R

/-- Compose maps of fixed-upper-bound left resolutions. -/
abbrev comp (m : Map f R S) (n : Map g S T) : Map (f ≫ g) R T :=
  LocalizerMorphism.LeftResolution.Map.comp m n

/-- Reindex a fixed-upper-bound resolution map along an equality of cochain maps. -/
abbrev reindex {f' : K ⟶ L} (e : f = f') (m : Map f R S) : Map f' R S :=
  LocalizerMorphism.LeftResolution.Map.reindex e m

/-- Regard a morphism in one fixed-bound resolution fiber as a map over the identity. -/
abbrev ofHom {R S : QuasiIsoFrom P a K} (m : R ⟶ S) : Map (𝟙 K) R S :=
  LocalizerMorphism.LeftResolution.Map.ofHom m

/-- Regard a fixed-bound resolution map over the identity as a morphism in one fiber. -/
abbrev toHom {R S : QuasiIsoFrom P a K} (m : Map (𝟙 K) R S) : R ⟶ S :=
  LocalizerMorphism.LeftResolution.Map.toHom m

/-- Morphisms in a fixed-bound resolution fiber are equivalent to maps over the identity. -/
abbrev homEquiv {R S : QuasiIsoFrom P a K} : (R ⟶ S) ≃ Map (𝟙 K) R S :=
  LocalizerMorphism.LeftResolution.Map.homEquiv

end Map

end CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom


