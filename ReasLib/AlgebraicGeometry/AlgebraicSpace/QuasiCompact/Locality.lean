module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Local criteria for quasi-compact morphisms of algebraic spaces

Quasi-compactness of a morphism of algebraic spaces is characterized by scheme-valued
and affine base changes, étale covers of the target, and Zariski coverings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace QuasiCompact

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- A morphism of algebraic spaces is quasi-compact iff every base change along
  a scheme is a quasi-compact morphism. Equivalently, `Z ×_Y X ⟶ Z` is
  quasi-compact for every scheme `Z` over `S` and morphism `ofOver Z ⟶ Y`. -/
theorem iff_forall_scheme :
    QuasiCompact f ↔ ∀ (Z : Over S) (g : ofOver Z ⟶ Y),
      QuasiCompact (pullback.snd f g) :=
  sorry

/-- A morphism of algebraic spaces is quasi-compact iff every base change along
  an affine scheme has quasi-compact source. Equivalently, the algebraic space
  `Z ×_Y X` is quasi-compact for every affine scheme `Z` over `S` and morphism
  `ofOver Z ⟶ Y`. -/
theorem iff_forall_affine :
    QuasiCompact f ↔ ∀ (Z : Over S) [IsAffine Z.left] (g : ofOver Z ⟶ Y),
      IsQuasiCompact (pullback f g) :=
  sorry

/-- A morphism of algebraic spaces is quasi-compact iff some surjective étale
  morphism from a scheme has quasi-compact base change. Equivalently, there is a
  scheme `V` over `S` and a surjective étale morphism `ofOver V ⟶ Y` such that
  `V ×_Y X ⟶ V` is quasi-compact. -/
theorem iff_exists_etale_scheme :
    QuasiCompact f ↔ ∃ (V : Over S) (g : ofOver V ⟶ Y),
      Etale g ∧ Surjective g ∧ QuasiCompact (pullback.snd f g) :=
  sorry

/-- A morphism of algebraic spaces is quasi-compact iff some surjective étale
  morphism of algebraic spaces has quasi-compact base change. Equivalently, there
  is a surjective étale morphism `Y' ⟶ Y` such that `Y' ×_Y X ⟶ Y'` is
  quasi-compact. -/
theorem iff_exists_etale :
    QuasiCompact f ↔ ∃ (Y' : AlgebraicSpace S) (g : Y' ⟶ Y),
      Etale g ∧ Surjective g ∧ QuasiCompact (pullback.snd f g) :=
  sorry

/-- A morphism of algebraic spaces is quasi-compact iff some Zariski covering of
  the target has quasi-compact inverse-image morphisms. Equivalently, there is a
  Zariski covering `Y = ⋃ Yᵢ` such that each `f⁻¹(Yᵢ) ⟶ Yᵢ`, realized as
  `pullback.snd f (𝒰.f i)`, is quasi-compact. -/
theorem iff_exists_zariskiCover :
    QuasiCompact f ↔ ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i, QuasiCompact (pullback.snd f (𝒰.f i)) :=
  sorry

end QuasiCompact

end AlgebraicGeometry.AlgebraicSpace
