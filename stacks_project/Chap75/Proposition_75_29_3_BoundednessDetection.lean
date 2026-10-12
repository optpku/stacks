/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Data.List.TFAE
public import Mathlib.Order.Filter.AtTopBot.Basic
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Structure
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Orthogonal
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_10_5_Gamma

/-!
# Boundedness detection by a perfect weak generator

On a quasi-compact quasi-separated algebraic space, a perfect weak generator of
`D_QCoh(𝒪_X)` detects membership of a derived quasicoherent object in the
bounded-above subcategory.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open DerivedCategory.TStructure
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- A perfect weak generator of `D_QCoh(𝒪_X)` detects boundedness above through eventual
shifted-Hom and Ext vanishing, derived global internal Hom, dual-tensor hypercohomology and
derived global sections; the same criteria may equivalently be required of every perfect
object of `D(𝒪_X)`. -/
theorem boundedAbove_tfae {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [MonoidalCategory (ModuleDerived X)] (H : MonoidalClosed (ModuleDerived X))
    (G E : DerivedQCoh X)
    (hG_perfect : ModuleDerived.IsPerfect G.obj) (hG_generator : IsWeakGenerator G) :
    List.TFAE
      [ (t.minus : ObjectProperty (ModuleDerived X)) E.obj
      , ∀ᶠ i : ℤ in Filter.atTop, Subsingleton (G.obj⟦-i⟧ ⟶ E.obj)
      , ∀ᶠ i : ℤ in Filter.atTop, Subsingleton (Ext⁽i⁾(G.obj, E.obj))
      , (t.minus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
          ((moduleDerivedGlobalSectionsAb X).obj ((ihomOf H G.obj).obj E.obj))
      , ∀ᶠ i : ℤ in Filter.atTop,
          IsZero (cohomologyAb X ((ihomOf H G.obj).obj (𝟙_ (ModuleDerived X)) ⊗ E.obj) i)
      , (t.minus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
          ((moduleDerivedGlobalSectionsAb X).obj
            ((ihomOf H G.obj).obj (𝟙_ (ModuleDerived X)) ⊗ E.obj))
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          ∀ᶠ i : ℤ in Filter.atTop, Subsingleton (P⟦-i⟧ ⟶ E.obj)
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          ∀ᶠ i : ℤ in Filter.atTop, Subsingleton (Ext⁽i⁾(P, E.obj))
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          (t.minus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
            ((moduleDerivedGlobalSectionsAb X).obj ((ihomOf H P).obj E.obj))
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          ∀ᶠ i : ℤ in Filter.atTop, IsZero (cohomologyAb X (P ⊗ E.obj) i)
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          (t.minus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
            ((moduleDerivedGlobalSectionsAb X).obj (P ⊗ E.obj))
      ] := sorry

/-- A perfect weak generator detects boundedness above exactly when its positive-degree Ext
groups into the object eventually vanish. -/
theorem boundedAbove_iff_extEventually {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (G E : DerivedQCoh X)
    (hG_perfect : ModuleDerived.IsPerfect G.obj) (hG_generator : IsWeakGenerator G) :
    (t.minus : ObjectProperty (ModuleDerived X)) E.obj ↔
      ∀ᶠ i : ℤ in Filter.atTop, Subsingleton (Ext⁽i⁾(G.obj, E.obj)) := sorry

/-- A derived quasicoherent object is bounded above exactly when tensoring it with every
perfect object of `D(𝒪_X)` has eventually vanishing global hypercohomology. -/
theorem boundedAbove_iff_perfectTensorCohomologyEventually
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [MonoidalCategory (ModuleDerived X)]
    (E : DerivedQCoh X) :
    (t.minus : ObjectProperty (ModuleDerived X)) E.obj ↔
      ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
        ∀ᶠ i : ℤ in Filter.atTop, IsZero (cohomologyAb X (P ⊗ E.obj) i) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
