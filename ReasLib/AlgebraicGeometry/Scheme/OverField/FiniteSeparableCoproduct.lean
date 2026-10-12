/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.FieldTheory.Separable
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Coproducts of spectra of finite separable field extensions

This file packages presentations of schemes over a field as coproducts of
spectra of finite separable field extensions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Explicit data presenting a scheme over a field as a coproduct of spectra of finite separable
field extensions of the base field. -/
structure SchemeAsDisjointUnionOfSpecFiniteSeparable (k : Type u) [Field k]
    (X : SchemeOverField k) where
  /-- The indexing type for the components. -/
  ι : Type u
  /-- The commutative algebra attached to each component. -/
  algebra : ι → CommAlgOverField k
  /-- Each component algebra is a field. -/
  isField : ∀ i, IsField (algebra i)
  /-- Each component algebra is finite-dimensional over the base field. -/
  finiteDimensional : ∀ i, FiniteDimensional k (algebra i)
  /-- Each component algebra is separable over the base field. -/
  isSeparable : ∀ i, Algebra.IsSeparable k (algebra i)
  /-- The scheme is isomorphic over the base field to the coproduct of the component spectra. -/
  iso :
    Over.mk X.hom ≅
      Over.mk
        (Limits.Sigma.desc fun i : ι ↦
          Spec.map (CommRingCat.ofHom (algebraMap k (algebra i))))

/-- Construct a finite-separable spectral coproduct presentation from its component data and
over-base isomorphism. -/
def SchemeAsDisjointUnionOfSpecFiniteSeparable.ofCoproduct
    {k : Type u} [Field k] {X : SchemeOverField k} (ι : Type u)
    (algebra : ι → CommAlgOverField k) (isField : ∀ i, IsField (algebra i))
    (finiteDimensional : ∀ i, FiniteDimensional k (algebra i))
    (isSeparable : ∀ i, Algebra.IsSeparable k (algebra i))
    (iso :
      Over.mk X.hom ≅
        Over.mk
          (Limits.Sigma.desc fun i : ι ↦
            Spec.map (CommRingCat.ofHom (algebraMap k (algebra i))))) :
    SchemeAsDisjointUnionOfSpecFiniteSeparable k X :=
  { ι, algebra, isField, finiteDimensional, isSeparable, iso }

/-- The canonical morphism from the coproduct of the component spectra to the base spectrum. -/
def SchemeAsDisjointUnionOfSpecFiniteSeparable.toSpec
    {k : Type u} [Field k] {X : SchemeOverField k}
    (D : SchemeAsDisjointUnionOfSpecFiniteSeparable k X) :
    (∐ fun i : D.ι ↦ Spec (CommRingCat.of (D.algebra i))) ⟶ Spec (CommRingCat.of k) :=
  Limits.Sigma.desc fun i : D.ι ↦
    Spec.map (CommRingCat.ofHom (algebraMap k (D.algebra i)))

/-- A finite-separable spectral coproduct presentation exposes field, finite-dimensional,
separable, and over-base isomorphism conditions on all of its components. -/
theorem SchemeAsDisjointUnionOfSpecFiniteSeparable.spec
    {k : Type u} [Field k] {X : SchemeOverField k}
    (D : SchemeAsDisjointUnionOfSpecFiniteSeparable k X) :
    (∀ i : D.ι, IsField (D.algebra i) ∧ FiniteDimensional k (D.algebra i) ∧
      Algebra.IsSeparable k (D.algebra i)) ∧
      Nonempty (Over.mk X.hom ≅ Over.mk D.toSpec) := sorry

end AlgebraicGeometry
