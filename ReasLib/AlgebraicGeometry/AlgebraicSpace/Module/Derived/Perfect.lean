/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.StrictlyPerfect
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.Additive
public import Mathlib.Algebra.Homology.Additive

public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale

namespace CochainComplex

/-- Restriction of cochain complexes of module sheaves to the slice over an étale
chart is induced by the identity of the restricted structure sheaf. -/
private abbrev restrictComplex {S : Scheme.{u}} (X : AlgebraicSpace S) (U : site X) :
    _root_.CochainComplex (Modules X) ℤ ⥤
      _root_.CochainComplex (SheafOfModules.{u} ((structureSheaf X).over U)) ℤ :=
  (SheafOfModules.pushforward.{u} (F := Over.forget U)
    (𝟙 ((structureSheaf X).over U))).mapHomologicalComplex (ComplexShape.up ℤ)

/-- A complex of module sheaves is perfect when every étale chart has a cover on
which the restricted complex receives a quasi-isomorphism from a strictly perfect
complex over the slice structure sheaf. -/
def IsPerfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    (complex : _root_.CochainComplex (Modules X) ℤ) : Prop :=
  ∀ U : site X, ∃ cover : (topology X).Cover U, ∀ chart : cover.Arrow,
    ∃ model : _root_.CochainComplex
        (SheafOfModules.{u} ((structureSheaf X).over chart.Y)) ℤ,
      SheafOfModules.CochainComplex.IsStrictlyPerfect model ∧
        ∃ comparison : model ⟶ (restrictComplex X chart.Y).obj complex,
          ∀ degree : ℤ, IsIso (HomologicalComplex.homologyMap comparison degree)

end CochainComplex

namespace ModuleDerived

/-- A derived module is perfect when it is isomorphic to the canonical derived
image of a perfect complex of module sheaves. -/
abbrev IsPerfect {S : Scheme.{u}} {X : AlgebraicSpace S} (object : ModuleDerived X) : Prop :=
  ∃ complex : _root_.CochainComplex (Modules X) ℤ,
    ∃ _ : object ≅ DerivedCategory.Q.obj complex, CochainComplex.IsPerfect complex

/-- Perfectness of a derived module is equivalent to the existence of a perfect
complex representative and an isomorphism to its canonical derived image. -/
theorem isPerfect_iff {S : Scheme.{u}} {X : AlgebraicSpace S} (object : ModuleDerived X) :
    IsPerfect object ↔
      ∃ complex : _root_.CochainComplex (Modules X) ℤ,
        ∃ _ : object ≅ DerivedCategory.Q.obj complex, CochainComplex.IsPerfect complex := sorry

end ModuleDerived

end AlgebraicGeometry.AlgebraicSpace.SmallEtale
