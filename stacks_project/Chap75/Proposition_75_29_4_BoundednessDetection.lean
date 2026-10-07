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

/-!
# Detecting boundedness below in `D_QCoh` on algebraic spaces

On a quasi-compact quasi-separated algebraic space, a perfect weak generator of
`D_QCoh(𝒪_X)` detects whether a derived quasicoherent object is bounded below, via
shifted Hom, Ext, global `RHom`, dual-tensor hypercohomology, and the same criteria
for every perfect object of `D(𝒪_X)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open AlgebraicGeometry.AlgebraicSpace.Modules
open DerivedCategory.TStructure
open scoped DerivedExt

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
    [MonoidalCategory (ModuleDerived X)] (H : MonoidalClosed (ModuleDerived X)) :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
        ((moduleDerivedGlobalSectionsAb X).obj ((ihomOf H G.obj).obj E.obj)) := sorry

/-- Boundedness below is equivalent to eventual vanishing of the global hypercohomology of
the tensor product of the dual of a perfect weak generator with the object. -/
theorem isBoundedBelow_iff_dualTensorCohomologyEventually
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    (H : MonoidalClosed (ModuleDerived X)) :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ →
        IsZero (cohomologyAb X ((ihomOf H G.obj).obj (𝟙_ (ModuleDerived X)) ⊗ E.obj) i) :=
  sorry

/-- Boundedness below is equivalent to boundedness below of the derived global sections of
the tensor product of the dual of a perfect weak generator with the object. -/
theorem isBoundedBelow_iff_dualTensorGlobalSections
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    (H : MonoidalClosed (ModuleDerived X)) :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
        ((moduleDerivedGlobalSectionsAb X).obj
          ((ihomOf H G.obj).obj (𝟙_ (ModuleDerived X)) ⊗ E.obj)) := sorry

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
    [MonoidalCategory (ModuleDerived X)] (H : MonoidalClosed (ModuleDerived X)) :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
        (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
          ((moduleDerivedGlobalSectionsAb X).obj ((ihomOf H P).obj E.obj)) := sorry

/-- Boundedness below is equivalent to eventual vanishing of the global hypercohomology of
the tensor product with every perfect ambient derived module. -/
theorem isBoundedBelow_iff_allPerfectTensorCohomologyEventually
    [MonoidalCategory (ModuleDerived X)] :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
        ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → IsZero (cohomologyAb X (P ⊗ E.obj) i) := sorry

/-- Boundedness below is equivalent to boundedness below of the derived global sections of
the tensor product with every perfect ambient derived module. -/
theorem isBoundedBelow_iff_allPerfectTensorGlobalSections
    [MonoidalCategory (ModuleDerived X)] :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
        (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
          ((moduleDerivedGlobalSectionsAb X).obj (P ⊗ E.obj)) := sorry

/-- A perfect weak generator detects boundedness below through shifted morphisms, Ext,
derived global internal Hom, dual-tensor hypercohomology and derived global sections; the
same criteria may equivalently be required of every perfect ambient derived module. -/
theorem boundedBelow_tfae
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    (H : MonoidalClosed (ModuleDerived X)) :
    List.TFAE
      [ (t.plus : ObjectProperty (ModuleDerived X)) E.obj
      , ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (G.obj⟦-i⟧ ⟶ E.obj)
      , ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(G.obj, E.obj))
      , (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
          ((moduleDerivedGlobalSectionsAb X).obj ((ihomOf H G.obj).obj E.obj))
      , ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ →
          IsZero (cohomologyAb X ((ihomOf H G.obj).obj (𝟙_ (ModuleDerived X)) ⊗ E.obj) i)
      , (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
          ((moduleDerivedGlobalSectionsAb X).obj
            ((ihomOf H G.obj).obj (𝟙_ (ModuleDerived X)) ⊗ E.obj))
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (P⟦-i⟧ ⟶ E.obj)
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(P, E.obj))
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
            ((moduleDerivedGlobalSectionsAb X).obj ((ihomOf H P).obj E.obj))
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → IsZero (cohomologyAb X (P ⊗ E.obj) i)
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
            ((moduleDerivedGlobalSectionsAb X).obj (P ⊗ E.obj))
      ] := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
