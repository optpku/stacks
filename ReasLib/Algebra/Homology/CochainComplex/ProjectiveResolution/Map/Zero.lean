/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution.Map
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Variable.Map.Zero

/-!
# Zero Maps of Projective Resolutions

This leaf specializes the variable-bound zero-map calculus to projective resolutions. It adds
only the source-facing names and comparison formula; the map data are owned by the neutral API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.ProjectiveResolution.Map

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
  {K L M : CochainComplex 𝒜 ℤ} {f : K ⟶ L} {g : L ⟶ M}
  {P : ProjectiveResolution K} {Q : ProjectiveResolution L}
  {R : ProjectiveResolution M}

/-- The zero map between two projective resolutions, lying over the zero cochain map. -/
abbrev zero (P : ProjectiveResolution K) (Q : ProjectiveResolution L) :
    Map (0 : K ⟶ L) P Q :=
  Minus.TermsIn.QuasiIsoFrom.Map.zero P Q

/-- The zero projective-resolution map has zero model morphism. -/
@[simp]
theorem zero_modelHom (P : ProjectiveResolution K) (Q : ProjectiveResolution L) :
    (zero P Q).modelHom = 0 := sorry

/-- The zero projective-resolution map has zero underlying cochain map. -/
@[simp]
theorem zero_hom (P : ProjectiveResolution K) (Q : ProjectiveResolution L) :
    (zero P Q).hom = 0 := sorry

/-- The zero projective-resolution map commutes with the augmentations. -/
theorem zero_naturality (P : ProjectiveResolution K) (Q : ProjectiveResolution L) :
    (zero P Q).hom ≫ Q.π = P.π ≫ (0 : K ⟶ L) := sorry

/-- Reindexing a zero projective-resolution map along a zero equality is trivial. -/
@[simp]
theorem reindex_zero (P : ProjectiveResolution K) (Q : ProjectiveResolution L)
    (e : (0 : K ⟶ L) = 0) : reindex e (zero P Q) = zero P Q := sorry

/-- Composing a zero projective-resolution map on the left gives zero. -/
@[simp]
theorem zero_comp (m : Map g Q R) :
    reindex Limits.zero_comp (comp (zero P Q) m) = zero P R := sorry

/-- Composing a zero projective-resolution map on the right gives zero. -/
@[simp]
theorem comp_zero (m : Map f P Q) :
    reindex Limits.comp_zero (comp m (zero Q R)) = zero P R := sorry

end CochainComplex.ProjectiveResolution.Map
