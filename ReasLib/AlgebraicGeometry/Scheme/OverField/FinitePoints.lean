module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Data.Finite.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry MonoidalCategory

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A scheme locally of finite type and quasi-compact over a finite field has only finitely
many points with values in a finite extension. -/
instance finite_schemeHom_specField
    {k L : Type u} [Field k] [Finite k] [Field L] [Algebra k L] [FiniteDimensional k L]
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    Finite (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶ X) := sorry

/-- A finite-type scheme over a finite field has finitely many rational points. -/
instance finite_homSpec {k : Type u} [Field k] [Finite k]
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] :
    Finite (𝟙_ (SchemeOverField k) ⟶ X) := by
  have h := finite_schemeHom_specField (k := k) (L := k) X
  have hid : Spec.map (CommRingCat.ofHom (algebraMap k k)) =
      𝟙 (Spec (CommRingCat.of k)) := by
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  change Finite (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X)
  rw [hid] at h
  exact h

end AlgebraicGeometry.SchemeOverField
