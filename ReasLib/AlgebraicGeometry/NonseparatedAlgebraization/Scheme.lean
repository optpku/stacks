/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Ideal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

/-!
# The non-separated finite-type algebraization example

Two copies of `Spec(k⟦t⟧[x])` are glued along `D(x) ∪ D(t)`, yielding a finite-type
morphism to `Spec(k⟦t⟧)` that is not separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.NonseparatedAlgebraization

/-- The ideal `I = (t)` in `k⟦t⟧`. -/
def adicIdeal (k : Type u) [Field k] : Ideal (PowerSeries k) :=
  Ideal.span {PowerSeries.X}

/-- The affine chart `Spec(A[x])` with `A = k⟦t⟧`. -/
def affineLine (k : Type u) [Field k] : Scheme.{u} :=
  Spec (.of (Polynomial (PowerSeries k)))

/-- The global section of `affineLine k` corresponding to the coordinate `x`. -/
def affineCoordinate (k : Type u) [Field k] : Γ(affineLine k, ⊤) :=
  (ΓSpecIso (.of (Polynomial (PowerSeries k)))).inv Polynomial.X

/-- The global section of `affineLine k` corresponding to the parameter `t`. -/
def formalParameter (k : Type u) [Field k] : Γ(affineLine k, ⊤) :=
  (ΓSpecIso (.of (Polynomial (PowerSeries k)))).inv
    (Polynomial.C (PowerSeries.X : PowerSeries k))

/-- The punctured open `D(x) ∪ D(t)`, the complement of the closed point `(x, t)`. -/
def puncturedOpen (k : Type u) [Field k] : (affineLine k).Opens :=
  (affineLine k).basicOpen (affineCoordinate k) ⊔
    (affineLine k).basicOpen (formalParameter k)

/-- The punctured open `D(x) ∪ D(t)` is not closed in `Spec(A[x])`. -/
theorem not_isClosed_puncturedOpen (k : Type u) [Field k] :
    ¬ IsClosed (puncturedOpen k : Set (affineLine k)) := sorry

/-- The scheme `X` obtained by doubling `Spec(A[x])` along `D(x) ∪ D(t)`. -/
def scheme (k : Type u) [Field k] : Scheme.{u} :=
  doubleAlong (puncturedOpen k)

/-- The doubled scheme `scheme k` is Noetherian. -/
instance instIsNoetherian_scheme (k : Type u) [Field k] : IsNoetherian (scheme k) := sorry

/-- The structure morphism of each affine chart, induced by `A → A[x]`. -/
def affineLineToSpec (k : Type u) [Field k] :
    affineLine k ⟶ Spec (.of (PowerSeries k)) :=
  Spec.map (CommRingCat.ofHom Polynomial.C)

/-- The structure morphism `X ⟶ Spec(A)` obtained by descending the two chart maps. -/
def toSpec (k : Type u) [Field k] : scheme k ⟶ Spec (.of (PowerSeries k)) :=
  DoubleAlong.desc (puncturedOpen k) (fun _ ↦ affineLineToSpec k) rfl

/-- The structure morphism `toSpec k` is of finite type. -/
instance instFiniteType_toSpec (k : Type u) [Field k] :
    Scheme.Hom.FiniteType (toSpec k) := sorry

/-- The structure morphism `X ⟶ Spec(A)` is not separated. -/
theorem not_isSeparated (k : Type u) [Field k] : ¬ IsSeparated (toSpec k) := sorry

/-- The algebraic space over `Spec(A)` presented by `scheme k`. -/
def spaceX (k : Type u) [Field k] : AlgebraicSpace (Spec (.of (PowerSeries k))) :=
  ofOver (Over.mk (toSpec k))

/-- The algebraic space over `Spec(A)` presented by `Spec(A)` itself. -/
def spaceB (k : Type u) [Field k] : AlgebraicSpace (Spec (.of (PowerSeries k))) :=
  ofOver (Over.mk (𝟙 (Spec (.of (PowerSeries k)))))

/-- The morphism of algebraic spaces over `Spec(A)` presented by `toSpec k`. -/
def spaceHom (k : Type u) [Field k] : spaceX k ⟶ spaceB k :=
  ofOverHomMk (toSpec k) (Category.comp_id (toSpec k))

/-- The algebraic-space morphism `spaceHom k` is of finite presentation. -/
instance instFinitePresentation_spaceHom (k : Type u) [Field k] :
    FinitePresentation (spaceHom k) := sorry

end AlgebraicGeometry.NonseparatedAlgebraization
