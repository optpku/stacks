module

public import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution.Map
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Variable.Map.Zero

/-!
# Zero Maps of Injective Resolutions

This leaf specializes the variable-bound zero-map calculus to injective resolutions. It adds
only the source-facing names and comparison formula; the map data are owned by the neutral API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.InjectiveResolution.Map

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
  {K L M : CochainComplex 𝒜 ℤ} {f : K ⟶ L} {g : L ⟶ M}
  {I : InjectiveResolution K} {J : InjectiveResolution L}
  {H : InjectiveResolution M}

/-- The zero map between two injective resolutions, lying over the zero cochain map. -/
abbrev zero (I : InjectiveResolution K) (J : InjectiveResolution L) :
    Map (0 : K ⟶ L) I J :=
  Plus.TermsIn.QuasiIsoTo.Map.zero I J

/-- The zero injective-resolution map has zero model morphism. -/
@[simp]
theorem zero_modelHom (I : InjectiveResolution K) (J : InjectiveResolution L) :
    (zero I J).modelHom = 0 := sorry

/-- The zero injective-resolution map has zero underlying cochain map. -/
@[simp]
theorem zero_hom (I : InjectiveResolution K) (J : InjectiveResolution L) :
    (zero I J).hom = 0 := sorry

/-- The zero injective-resolution map commutes with the augmentations. -/
theorem zero_naturality (I : InjectiveResolution K) (J : InjectiveResolution L) :
    I.ι ≫ (zero I J).hom = (0 : K ⟶ L) ≫ J.ι := sorry

/-- Reindexing a zero injective-resolution map along a zero equality is trivial. -/
@[simp]
theorem reindex_zero (I : InjectiveResolution K) (J : InjectiveResolution L)
    (e : (0 : K ⟶ L) = 0) : reindex e (zero I J) = zero I J := sorry

/-- Composing a zero injective-resolution map on the left gives zero. -/
@[simp]
theorem zero_comp (m : Map g J H) :
    reindex Limits.zero_comp (comp (zero I J) m) = zero I H := sorry

/-- Composing a zero injective-resolution map on the right gives zero. -/
@[simp]
theorem comp_zero (m : Map f I J) :
    reindex Limits.comp_zero (comp m (zero J H)) = zero I H := sorry

end CochainComplex.InjectiveResolution.Map


