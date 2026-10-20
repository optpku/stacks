module

public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Data.List.TFAE
public import Mathlib.Order.Filter.AtTopBot.Basic
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Structure
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Monoidal
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Orthogonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections.Abelian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Dual

/-!
# Boundedness detection by a perfect weak generator

On a quasi-compact quasi-separated algebraic space, a perfect weak generator of
`D_QCoh(𝒪_X)` detects membership of a derived quasicoherent object in the
bounded-above or bounded-below subcategory.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open DerivedCategory.TStructure
open scoped DerivedExt CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- A perfect weak generator of `D_QCoh(𝒪_X)` detects boundedness above through eventual
shifted-Hom and Ext vanishing, derived global internal Hom, dual-tensor hypercohomology and
derived global sections; the same criteria may equivalently be required of every perfect
object of `D(𝒪_X)`. -/
theorem boundedAbove_tfae {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    (H : MonoidalClosed (ModuleDerived X))
    (M : DerivedCategory.DerivedTensor.Right.Monoidal.Model (C := Modules X))
    (G E : DerivedQCoh X)
    (hG_perfect : ModuleDerived.IsPerfect G.obj) (hG_generator : IsWeakGenerator G) :
    List.TFAE
      [ (t.minus : ObjectProperty (ModuleDerived X)) E.obj
      , ∀ᶠ i : ℤ in Filter.atTop, Subsingleton (G.obj⟦-i⟧ ⟶ E.obj)
      , ∀ᶠ i : ℤ in Filter.atTop, Subsingleton (Ext⁽i⁾(G.obj, E.obj))
      , (t.minus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
          ((moduleDerivedGlobalSectionsAb X).obj ((ihomOf H G.obj).obj E.obj))
      , ∀ᶠ i : ℤ in Filter.atTop,
          IsZero (cohomologyAb X ((ihomOf H G.obj).obj ((DerivedCategory.singleFunctor (Modules X) 0).obj (𝟙_ (Modules X))) ⊗ᴸ E.obj) i)
      , (t.minus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
          ((moduleDerivedGlobalSectionsAb X).obj
            ((ihomOf H G.obj).obj ((DerivedCategory.singleFunctor (Modules X) 0).obj (𝟙_ (Modules X))) ⊗ᴸ E.obj))
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          ∀ᶠ i : ℤ in Filter.atTop, Subsingleton (P⟦-i⟧ ⟶ E.obj)
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          ∀ᶠ i : ℤ in Filter.atTop, Subsingleton (Ext⁽i⁾(P, E.obj))
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          (t.minus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
            ((moduleDerivedGlobalSectionsAb X).obj ((ihomOf H P).obj E.obj))
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          ∀ᶠ i : ℤ in Filter.atTop, IsZero (cohomologyAb X (P ⊗ᴸ E.obj) i)
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          (t.minus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
            ((moduleDerivedGlobalSectionsAb X).obj (P ⊗ᴸ E.obj))
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
perfect object of `D(𝒪_X)` by derived tensor has eventually vanishing global hypercohomology. -/
theorem boundedAbove_iff_perfectTensorCohomologyEventually
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (E : DerivedQCoh X) :
    (t.minus : ObjectProperty (ModuleDerived X)) E.obj ↔
      ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
        ∀ᶠ i : ℤ in Filter.atTop, IsZero (cohomologyAb X (P ⊗ᴸ E.obj) i) := sorry

/-- Boundedness below is equivalent to eventual vanishing of shifted morphisms from a
perfect weak generator. -/
theorem isBoundedBelow_iff_homShiftEventually
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (G E : DerivedQCoh X)
    (hG_perfect : ModuleDerived.IsPerfect G.obj) (hG_generator : IsWeakGenerator G) :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (G.obj⟦-i⟧ ⟶ E.obj) := sorry

/-- Boundedness below is equivalent to eventual negative-degree Ext vanishing against a
perfect weak generator. -/
theorem isBoundedBelow_iff_extEventually
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (G E : DerivedQCoh X)
    (hG_perfect : ModuleDerived.IsPerfect G.obj) (hG_generator : IsWeakGenerator G) :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(G.obj, E.obj)) := sorry

/-- Boundedness below is equivalent to boundedness below of the derived global internal Hom
from a perfect weak generator. -/
theorem isBoundedBelow_iff_globalHom
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (G E : DerivedQCoh X)
    (hG_perfect : ModuleDerived.IsPerfect G.obj) (hG_generator : IsWeakGenerator G) :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
        ((moduleDerivedGlobalSectionsAb X).obj (ModuleDerived.InternalHom.obj G.obj E.obj)) := sorry

/-- Boundedness below is equivalent to eventual vanishing of the global hypercohomology of
the tensor product of the dual of a perfect weak generator with the object. -/
theorem isBoundedBelow_iff_dualTensorCohomologyEventually
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (G E : DerivedQCoh X)
    (hG_perfect : ModuleDerived.IsPerfect G.obj) (hG_generator : IsWeakGenerator G) :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ →
        IsZero (cohomologyAb X (ModuleDerived.dual G.obj ⊗ᴸ E.obj) i) := sorry

/-- Boundedness below is equivalent to boundedness below of the derived global sections of
the tensor product of the dual of a perfect weak generator with the object. -/
theorem isBoundedBelow_iff_dualTensorGlobalSections
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (G E : DerivedQCoh X)
    (hG_perfect : ModuleDerived.IsPerfect G.obj) (hG_generator : IsWeakGenerator G) :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
        ((moduleDerivedGlobalSectionsAb X).obj
          (ModuleDerived.dual G.obj ⊗ᴸ E.obj)) := sorry

/-- Boundedness below is equivalent to eventual vanishing of shifted morphisms from every
perfect ambient derived module. -/
theorem isBoundedBelow_iff_allPerfectHomShiftEventually
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (E : DerivedQCoh X) :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
        ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (P⟦-i⟧ ⟶ E.obj) := sorry

/-- Boundedness below is equivalent to eventual negative-degree Ext vanishing against every
perfect ambient derived module. -/
theorem isBoundedBelow_iff_allPerfectExtEventually
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (E : DerivedQCoh X) :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
        ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(P, E.obj)) := sorry

/-- Boundedness below is equivalent to boundedness below of the derived global internal Hom
from every perfect ambient derived module. -/
theorem isBoundedBelow_iff_allPerfectGlobalHom
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (E : DerivedQCoh X) :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
        (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
          ((moduleDerivedGlobalSectionsAb X).obj (ModuleDerived.InternalHom.obj P E.obj)) := sorry

/-- Boundedness below is equivalent to eventual vanishing of the global hypercohomology of
the tensor product with every perfect ambient derived module. -/
theorem isBoundedBelow_iff_allPerfectTensorCohomologyEventually
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (E : DerivedQCoh X) :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
        ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → IsZero (cohomologyAb X (P ⊗ᴸ E.obj) i) := sorry

/-- Boundedness below is equivalent to boundedness below of the derived global sections of
the tensor product with every perfect ambient derived module. -/
theorem isBoundedBelow_iff_allPerfectTensorGlobalSections
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (E : DerivedQCoh X) :
    (t.plus : ObjectProperty (ModuleDerived X)) E.obj ↔
      ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
        (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
          ((moduleDerivedGlobalSectionsAb X).obj (P ⊗ᴸ E.obj)) := sorry

/-- A perfect weak generator detects boundedness below through shifted morphisms, Ext,
derived global internal Hom, dual-tensor hypercohomology and derived global sections; the
same criteria may equivalently be required of every perfect ambient derived module. -/
theorem boundedBelow_tfae
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (G E : DerivedQCoh X)
    (hG_perfect : ModuleDerived.IsPerfect G.obj) (hG_generator : IsWeakGenerator G) :
    List.TFAE
      [ (t.plus : ObjectProperty (ModuleDerived X)) E.obj
      , ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (G.obj⟦-i⟧ ⟶ E.obj)
      , ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(G.obj, E.obj))
      , (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
          ((moduleDerivedGlobalSectionsAb X).obj (ModuleDerived.InternalHom.obj G.obj E.obj))
      , ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ →
          IsZero (cohomologyAb X (ModuleDerived.dual G.obj ⊗ᴸ E.obj) i)
      , (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
          ((moduleDerivedGlobalSectionsAb X).obj
            (ModuleDerived.dual G.obj ⊗ᴸ E.obj))
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (P⟦-i⟧ ⟶ E.obj)
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(P, E.obj))
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
            ((moduleDerivedGlobalSectionsAb X).obj (ModuleDerived.InternalHom.obj P E.obj))
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → IsZero (cohomologyAb X (P ⊗ᴸ E.obj) i)
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
            ((moduleDerivedGlobalSectionsAb X).obj (P ⊗ᴸ E.obj))
      ] := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
