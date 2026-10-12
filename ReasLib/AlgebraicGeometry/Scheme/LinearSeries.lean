/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Sections

@[expose] public section

open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A linear series of degree `d` and dimension `r` on `X` consists of an invertible module of
degree `d` together with an `(r + 1)`-dimensional subspace of its global sections. -/
structure LinearSeries {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (d r : ℕ) where
  /-- The invertible module underlying the linear series. -/
  lineBundle : X.left.Modules
  /-- The proof that the underlying module is invertible. -/
  isInvertible : Scheme.Modules.Invertible lineBundle
  /-- The chosen subspace of global sections. -/
  sections : Submodule k (Scheme.Hom.globalSectionsMod X.hom lineBundle)
  /-- The chosen subspace is finite-dimensional over the base field. -/
  finiteDimensional : FiniteDimensional k sections
  /-- The underlying invertible module has degree `d`. -/
  degree_eq : @Scheme.Modules.curveDegreeOfInvertible k _ X.left X.hom _ hdim
      lineBundle isInvertible = (d : ℤ)
  /-- The chosen subspace has dimension `r + 1`. -/
  finrank_eq : Module.finrank k sections = r + 1

namespace LinearSeries

/-- Construct a linear series from an invertible module and a finite-dimensional subspace of its
global sections with the prescribed degree and dimension. -/
def ofSubmodule {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (d r : ℕ) (L : X.left.Modules)
    [hL : Scheme.Modules.Invertible L]
    (W : Submodule k (Scheme.Hom.globalSectionsMod X.hom L))
    [hW : FiniteDimensional k W]
    (degree_eq : Scheme.Modules.curveDegreeOfInvertible X.hom hdim L = (d : ℤ))
    (finrank_eq : Module.finrank k W = r + 1) : LinearSeries X hdim d r where
  lineBundle := L
  isInvertible := hL
  sections := W
  finiteDimensional := hW
  degree_eq := degree_eq
  finrank_eq := finrank_eq

/-- The inclusion of the chosen subspace into all global sections. -/
def inclusion {k : Type u} [Field k] {X : SchemeOverField k} [IsProper X.hom]
    {hdim : topologicalKrullDim X.left ≤ 1} {d r : ℕ} (g : LinearSeries X hdim d r) :
    ModuleCat.of k g.sections ⟶ Scheme.Hom.globalSectionsMod X.hom g.lineBundle :=
  ConcreteCategory.ofHom (C := ModuleCat k) g.sections.subtype

/-- Applying the inclusion of a linear series gives the underlying global section. -/
theorem inclusion_apply {k : Type u} [Field k] {X : SchemeOverField k} [IsProper X.hom]
    {hdim : topologicalKrullDim X.left ≤ 1} {d r : ℕ} (g : LinearSeries X hdim d r)
    (s : g.sections) : g.inclusion s = s := sorry

/-- The degree and dimension equations satisfied by a linear series. -/
theorem spec {k : Type u} [Field k] {X : SchemeOverField k} [IsProper X.hom]
    {hdim : topologicalKrullDim X.left ≤ 1} {d r : ℕ} (g : LinearSeries X hdim d r) :
    @Scheme.Modules.curveDegreeOfInvertible k _ X.left X.hom _ hdim
        g.lineBundle g.isInvertible = (d : ℤ) ∧
      Module.finrank k g.sections = r + 1 := sorry

/-- A proper scheme of topological dimension at most one over a field admitting a linear series
of degree `d` and dimension `r` admits one of the same degree and every dimension `s ≤ r`. -/
theorem exists_of_dimension_le {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) {d r : ℕ}
    (h : Nonempty (LinearSeries X hdim d r)) (s : ℕ) (hs : s ≤ r) :
    Nonempty (LinearSeries X hdim d s) := sorry

end LinearSeries

end AlgebraicGeometry
