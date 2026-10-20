module

public import Mathlib.RingTheory.Congruence.Hom
public import ReasLib.Geometry.Manifold.Complex.CompactRiemannSurface
public import ReasLib.Geometry.Manifold.Complex.MeromorphicFunctionField

/-!
# Pullback of meromorphic functions

Nonconstant holomorphic maps pull meromorphic functions back by composition. The quotient map
below descends composition of representatives through codiscrete equality, so values assigned
at poles do not affect pullback.
-/

@[expose] public section

open scoped Manifold MeromorphicFunctionField Topology
open CategoryTheory

noncomputable section

universe u

-- Match the normed-group and scalar structures used by the meromorphic-field owner.
-- They normalize mathlib's inherited complex instances in chart expressions.
noncomputable local instance : NormedAddCommGroup ℂ :=
  NonUnitalNormedRing.toNormedAddCommGroup

noncomputable local instance : NormedSpace ℂ ℂ := NormedAlgebra.toNormedSpace ℂ

namespace MeromorphicFunctionField

variable {X Y Z : CompactRiemannSurface.{u}}

/-- Composition with a holomorphic map preserves meromorphic representatives. -/
theorem IsMeromorphic.comp (f : CompactRiemannSurfaceHom X Y)
    {g : Y → ℂ} (hg : IsMeromorphic Y g) :
    IsMeromorphic X (g ∘ f) := sorry

/-- A nonconstant holomorphic map preserves codiscrete equality under pullback. Its discrete
fibers prevent exceptional point values in the target from becoming open sets in the source. -/
theorem eventuallyEq_comp (f : CompactRiemannSurfaceHom X Y) (hf : f.IsNonconstant)
    {g h : Y → ℂ} (hgh : g =ᶠ[Filter.codiscrete Y] h) :
    g ∘ f =ᶠ[Filter.codiscrete X] h ∘ f := sorry

/-- Composition of meromorphic representatives, as a map of complex algebras. -/
def Representative.pullback (f : CompactRiemannSurfaceHom X Y) :
    Representative.subalgebra Y →ₐ[ℂ] Representative.subalgebra X where
  toFun g := ⟨g ∘ f, IsMeromorphic.comp (X := X) (Y := Y) f (by
    change IsMeromorphic Y (g : Y → ℂ)
    exact g.property)⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' g h := by
    apply Subtype.ext
    rfl
  map_zero' := by
    apply Subtype.ext
    rfl
  map_add' g h := by
    apply Subtype.ext
    rfl
  commutes' c := by
    apply Subtype.ext
    rfl

/-- Pullback of meromorphic functions by a nonconstant holomorphic map. -/
def pullback (f : CompactRiemannSurfaceHom X Y) (hf : f.IsNonconstant) :
    ℂ(Y) →ₐ[ℂ] ℂ(X) :=
  (Representative.con Y).liftₐ
    (((Representative.con X).mkₐ ℂ).comp
      (Representative.pullback (X := X) (Y := Y) f)) (by
      intro g h hgh
      apply (Representative.con X).eq.mpr
      change (g : Y → ℂ) ∘ f =ᶠ[Filter.codiscrete X] (h : Y → ℂ) ∘ f
      exact eventuallyEq_comp (X := X) (Y := Y) f hf hgh)

/-- Pullback is composition on a representative. -/
@[simp]
theorem pullback_mk (f : CompactRiemannSurfaceHom X Y) (hf : f.IsNonconstant)
    (g : Y → ℂ) (hg : IsMeromorphic Y g) :
    pullback (X := X) (Y := Y) f hf (mk Y g hg) =
      mk X (g ∘ f) (IsMeromorphic.comp (X := X) (Y := Y) f hg) := rfl

/-- Pullback along the identity is the identity algebra map. -/
@[simp]
theorem pullback_id (X : CompactRiemannSurface.{u}) :
    pullback (X := X) (Y := X) (𝟙 X)
      (CompactRiemannSurface.nonconstantHom.id_mem X) =
      AlgHom.id ℂ ℂ(X) := sorry

/-- Pullback reverses composition of nonconstant holomorphic maps. -/
theorem pullback_comp (f : CompactRiemannSurfaceHom X Y) (hf : f.IsNonconstant)
    (g : CompactRiemannSurfaceHom Y Z) (hg : g.IsNonconstant) :
    pullback (X := X) (Y := Z) (f ≫ g : X ⟶ Z)
      (CompactRiemannSurface.nonconstantHom.comp_mem (f : X ⟶ Y) (g : Y ⟶ Z) hf hg) =
      (pullback (X := X) (Y := Y) f hf).comp
        (pullback (X := Y) (Y := Z) g hg) := sorry

end MeromorphicFunctionField
