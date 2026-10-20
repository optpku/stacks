module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Presentation

/-!
# Maps between relative projective spectra

This file packages the domain, restricted scheme morphism, and degreewise twist comparisons
associated to a map between relative projective spectra.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry

variable {S X Y : Scheme.{u}}
variable {pX : X ⟶ S} {pY : Y ⟶ S}

/-- A map between relative projective spectra consists of an open domain, a morphism from that
domain over the base, and degreewise comparison maps between the corresponding twists. -/
structure RelativeProjMap
    (P𝒜 : RelativeProjPresentation pX)
    (Pℬ : RelativeProjPresentation pY)
    (φ : P𝒜.algebra ⟶ Pℬ.algebra) where
  /-- The open subset on which the induced morphism is defined. -/
  domain : Y.Opens
  /-- The induced morphism from the open domain. -/
  map : domain.toScheme ⟶ X
  /-- The induced morphism commutes with the structural morphisms to the base. -/
  map_over_base : map ≫ pX = domain.ι ≫ pY
  /-- The degreewise comparison from the pullback of the source twist to the restricted target
  twist. -/
  theta :
    ∀ n : ℤ,
      (Scheme.Modules.pullback map).obj (P𝒜.twist n) ⟶
        (Pℬ.twist n).restrict domain.ι

namespace RelativeProjMap

/-- The underlying morphism of a relative projective spectrum map, regarded as a morphism over
the common base scheme. -/
def overHom
    {P𝒜 : RelativeProjPresentation pX}
    {Pℬ : RelativeProjPresentation pY}
    {φ : P𝒜.algebra ⟶ Pℬ.algebra}
    (r : RelativeProjMap P𝒜 Pℬ φ) :
    Over.mk (r.domain.ι ≫ pY) ⟶ Over.mk pX :=
  Over.homMk r.map r.map_over_base

end RelativeProjMap

end AlgebraicGeometry
