/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.OverField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsolatedSingularities

/-! # Families of curves with isolated singularities -/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of families of curves whose structure morphism has
isolated singularities. -/
def isolatedSingularities (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ IsolatedSingularities (hom P)

/-- Membership in `isolatedSingularities` is isolated singularities of the
structure morphism. -/
theorem isolatedSingularities_iff {S : Scheme.{u}} (P : Obj S) :
    isolatedSingularities S P ↔ IsolatedSingularities (hom P) :=
  Iff.rfl

/-- The isolated-singularities property of families of curves is closed under
isomorphisms. -/
instance instIsClosedUnderIsomorphisms_isolatedSingularities
    (S : Scheme.{u}) : (isolatedSingularities S).IsClosedUnderIsomorphisms :=
  sorry

/-- Every family of curves has a largest open on its base with isolated
singularities. Its inverse image is the corresponding largest open after every
cartesian change of family, and membership is equivalent to factorization of
the base morphism through this open. -/
theorem isolatedSingularities_openOnBase {S : Scheme.{u}} (P : Obj S) :
    ∃ U : OpenSubspace (ofOver (base P)),
      IsLargestIsolatedSingularitiesOpen (hom P) U ∧
        ∀ {Q : Obj S} (φ : Q ⟶ P),
          IsLargestIsolatedSingularitiesOpen (hom Q)
              (U.inverseImage (ofOverMap (baseMap φ))) ∧
            (isolatedSingularities S Q ↔
              ∃ χ : ofOver (base Q) ⟶ U.X,
                χ ≫ U.ι = ofOverMap (baseMap φ)) :=
  sorry

/-- The full subcategory of families of curves with isolated singularities is
fibred in groupoids over the category of schemes over the base. -/
instance instIsFiberedInGroupoids_isolatedSingularities (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids ((isolatedSingularities S).ι ⋙ p S) :=
  sorry

/-- For a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ Curves` factors through `Curves⁺` if and only if the singular
locus of `X ⟶ S` endowed with any/some closed subspace structure is finite
over `S`. -/
theorem classifying_factorsThrough_isolatedSingularities_iff
    {S : Scheme.{u}} (P : Obj S) :
    isolatedSingularities S P ↔
      ∀ T : ClosedSubspaceStructure (nonsmoothLocusClosed (hom P)),
        IsFinite (T.ι ≫ hom P) :=
  sorry

/-- For `X` a proper scheme over a field `k` of
dimension `≤ 1`, the classifying morphism `Spec k ⟶ Curves` factors through
`Curves⁺` if and only if `X ⟶ Spec k` is smooth except at finitely many
points. -/
theorem classifying_factorsThrough_isolatedSingularities_iff_finiteNonsmooth
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    isolatedSingularities (Spec (CommRingCat.of k))
        (mkOfSchemeOverField X hdim) ↔
      Set.Finite (setOf fun x : X.left ↦ ¬ X.hom.SmoothAt x) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
