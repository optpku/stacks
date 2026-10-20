/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Adjoin.FGBaseChange
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.CommAlgCat.FilteredColimit
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Affine

/-!
# Closure of Affine Geometric Irreducibility

This leaf owns the affine closure properties of geometric irreducibility over
a field.  The primary predicates remain mathlib's morphism-level
`GeometricallyIrreducible`; the statements here are the reusable algebra
presentations needed for subalgebras, finitely generated tests, and filtered
colimits.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits CommRingCat

universe u v

namespace AlgebraicGeometry.SchemeOverField

namespace GeometricallyIrreducible

section

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

/-- Geometric irreducibility descends along an injective morphism of affine algebras over a
field. -/
@[stacks 037N "injective affine descent"]
theorem of_injective
    {B : Type u} [CommRing B] [Algebra k B]
    (f : B →ₐ[k] A) (hf : Function.Injective f)
    (hA : GeometricallyIrreducible (Spec.map (ofHom (algebraMap k A)))) :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k B))) := sorry

/-- Lemma 10.47.6 (1) (Tag 037N): every subalgebra of a geometrically irreducible affine
algebra over a field is geometrically irreducible. -/
@[stacks 037N]
theorem of_subalgebra
    (S : Subalgebra k A)
    (hA : GeometricallyIrreducible (Spec.map (ofHom (algebraMap k A)))) :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k S))) := sorry

/-- A subalgebra of a geometrically irreducible affine algebra inherits the canonical
geometric-irreducibility instance. -/
@[stacks 037N "subalgebra instance"]
instance instSubalgebra
    (S : Subalgebra k A)
    [GeometricallyIrreducible (Spec.map (ofHom (algebraMap k A)))] :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k S))) := sorry

/-- Lemma 10.47.6 (2) (Tag 037N): geometric irreducibility of every finitely generated
subalgebra implies geometric irreducibility of the ambient affine algebra. -/
@[stacks 037N]
theorem of_forall_fg
    (h : ∀ S : Subalgebra k A, S.FG →
      GeometricallyIrreducible (Spec.map (ofHom (algebraMap k S)))) :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k A))) := sorry

end

section

variable {k : Type u} {I : Type v} [Field k]
variable [Category I] [IsFilteredOrEmpty I]

/-- Lemma 10.47.6 (3) (Tag 037N): a filtered-or-empty colimit of geometrically irreducible
affine algebras over a field is geometrically irreducible. -/
@[stacks 037N]
theorem of_filteredColimit
    (F : I ⥤ CommAlgCat.{u} k) [HasColimit F]
    (hF : ∀ i, GeometricallyIrreducible
      (Spec.map (ofHom (algebraMap k (F.obj i))))) :
    GeometricallyIrreducible
      (Spec.map (ofHom (algebraMap k (colimit F : CommAlgCat.{u} k)))) := sorry

end

end GeometricallyIrreducible

end AlgebraicGeometry.SchemeOverField
