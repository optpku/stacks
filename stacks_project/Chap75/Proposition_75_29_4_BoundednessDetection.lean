/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Structure
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Orthogonal
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_10_5_Gamma
public import stacks_project.Chap75.Lemma_75_5_6_Tensor

/-!
# Detecting boundedness below in `D_QCoh` on algebraic spaces

On a quasi-compact quasi-separated algebraic space, a perfect weak generator of
`D_QCoh(𝒪_X)` detects whether a derived quasicoherent object is bounded below, via
shifted Hom, Ext, global `RHom`, dual-tensor hypercohomology, and the same criteria
for every perfect object of `D(𝒪_X)`.

All tensor criteria use geometric `⊗ᴸ`. An explicit closed owner is used only
with a natural comparison from its fixed-right tensor to `DerivedTensor.Right.functor`.
Duals evaluate that identified internal Hom at the actual degree-zero structure
sheaf, so no unverified monoidal unit is substituted for the source object.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.DerivedCategory DerivedCategory.TStructure
open _root_.DerivedCategory
open scoped DerivedExt DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
variable (G E : DerivedQCoh X)
variable (hG_perfect : ModuleDerived.IsPerfect G.obj)
variable (hG_generator : IsWeakGenerator G)

include hG_perfect hG_generator

/-- Boundedness below is equivalent to eventual vanishing of shifted morphisms from a
perfect weak generator. -/
theorem isBoundedBelow_iff_homShiftEventually :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (G.obj⟦-i⟧ ⟶ E.obj) := sorry

/-- Boundedness below is equivalent to eventual negative-degree Ext vanishing against a
perfect weak generator. -/
theorem isBoundedBelow_iff_extEventually :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(G.obj, E.obj)) := sorry

/-- Boundedness below is equivalent to boundedness below of the derived global internal Hom
from a perfect weak generator. -/
theorem isBoundedBelow_iff_globalHom
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    (H : MonoidalClosed (ModuleDerived X))
    (tensorComparison : ∀ P : ModuleDerived X,
      MonoidalCategory.tensorRight P ≅ DerivedTensor.Right.functor P) :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
        ((moduleDerivedGlobalSectionsAb X).obj ((ihomOf H G.obj).obj E.obj)) := sorry

/-- Boundedness below is equivalent to eventual vanishing of the global hypercohomology of
the tensor product of the dual of a perfect weak generator with the object. -/
theorem isBoundedBelow_iff_dualTensorCohomologyEventually
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    (H : MonoidalClosed (ModuleDerived X))
    (tensorComparison : ∀ P : ModuleDerived X,
      MonoidalCategory.tensorRight P ≅ DerivedTensor.Right.functor P) :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ →
        IsZero (cohomologyAb X ((ihomOf H G.obj).obj ((singleFunctor X.Modules 0).obj (𝟙_ X.Modules)) ⊗ᴸ E.obj) i) :=
  sorry

/-- Boundedness below is equivalent to boundedness below of the derived global sections of
the tensor product of the dual of a perfect weak generator with the object. -/
theorem isBoundedBelow_iff_dualTensorGlobalSections
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    (H : MonoidalClosed (ModuleDerived X))
    (tensorComparison : ∀ P : ModuleDerived X,
      MonoidalCategory.tensorRight P ≅ DerivedTensor.Right.functor P) :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
        ((moduleDerivedGlobalSectionsAb X).obj
          ((ihomOf H G.obj).obj ((singleFunctor X.Modules 0).obj (𝟙_ X.Modules)) ⊗ᴸ E.obj)) := sorry

/-- Boundedness below is equivalent to eventual vanishing of shifted morphisms from every
perfect ambient derived module. -/
theorem isBoundedBelow_iff_allPerfectHomShiftEventually :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
        ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (P⟦-i⟧ ⟶ E.obj) := sorry

/-- Boundedness below is equivalent to eventual negative-degree Ext vanishing against every
perfect ambient derived module. -/
theorem isBoundedBelow_iff_allPerfectExtEventually :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
        ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(P, E.obj)) := sorry

/-- Boundedness below is equivalent to boundedness below of the derived global internal Hom
from every perfect ambient derived module. -/
theorem isBoundedBelow_iff_allPerfectGlobalHom
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    (H : MonoidalClosed (ModuleDerived X))
    (tensorComparison : ∀ P : ModuleDerived X,
      MonoidalCategory.tensorRight P ≅ DerivedTensor.Right.functor P) :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
        (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
          ((moduleDerivedGlobalSectionsAb X).obj ((ihomOf H P).obj E.obj)) := sorry

/-- Boundedness below is equivalent to eventual vanishing of the global hypercohomology of
the tensor product with every perfect ambient derived module. -/
theorem isBoundedBelow_iff_allPerfectTensorCohomologyEventually :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
        ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → IsZero (cohomologyAb X (P ⊗ᴸ E.obj) i) := sorry

/-- Boundedness below is equivalent to boundedness below of the derived global sections of
the tensor product with every perfect ambient derived module. -/
theorem isBoundedBelow_iff_allPerfectTensorGlobalSections :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
        (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
          ((moduleDerivedGlobalSectionsAb X).obj (P ⊗ᴸ E.obj)) := sorry

/-- A perfect weak generator detects boundedness below through shifted morphisms, Ext,
derived global internal Hom, dual-tensor hypercohomology and derived global sections; the
same criteria may equivalently be required of every perfect ambient derived module. -/
theorem boundedBelow_tfae
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    (H : MonoidalClosed (ModuleDerived X))
    (tensorComparison : ∀ P : ModuleDerived X,
      MonoidalCategory.tensorRight P ≅ DerivedTensor.Right.functor P) :
    List.TFAE
      [ (t.plus : ObjectProperty (ModuleDerived X)) E.obj
      , ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (G.obj⟦-i⟧ ⟶ E.obj)
      , ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(G.obj, E.obj))
      , (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
          ((moduleDerivedGlobalSectionsAb X).obj ((ihomOf H G.obj).obj E.obj))
      , ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ →
          IsZero (cohomologyAb X ((ihomOf H G.obj).obj ((singleFunctor X.Modules 0).obj (𝟙_ X.Modules)) ⊗ᴸ E.obj) i)
      , (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
          ((moduleDerivedGlobalSectionsAb X).obj
            ((ihomOf H G.obj).obj ((singleFunctor X.Modules 0).obj (𝟙_ X.Modules)) ⊗ᴸ E.obj))
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (P⟦-i⟧ ⟶ E.obj)
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(P, E.obj))
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
            ((moduleDerivedGlobalSectionsAb X).obj ((ihomOf H P).obj E.obj))
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → IsZero (cohomologyAb X (P ⊗ᴸ E.obj) i)
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
            ((moduleDerivedGlobalSectionsAb X).obj (P ⊗ᴸ E.obj))
      ] := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
