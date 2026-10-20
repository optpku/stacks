/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.CategoryTheory.Category.Preorder
public import ReasLib.AlgebraicGeometry.Scheme.LocallyClosedReduction
public import ReasLib.Order.Induced
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Colimit

/-!
# Admissible finite supports on a base change

The small preorder of locally closed subsets of `|X_V|` whose reduced induced
scheme is finite over `V`, together with an ambient open in which the subset is
closed. This is the index category of `colim_Z H_Z(F)`.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace FiniteSupport

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]

/-- An admissible locally closed subset of `|X_V|`, together with an ambient open
in which it is closed, whose reduced induced scheme is finite over `V`. -/
structure AdmissiblePresentation (V : Y.Etale) where
  /-- The locally closed subset `Z ⊂ |X_V|`. -/
  subset : LocallyCloseds (baseChangeScheme f V)
  /-- An open of `X_V` containing `Z` as a closed subset. -/
  ambient : (baseChangeScheme f V).Opens
  /-- `Z` is contained in the ambient open. -/
  subset_le_ambient : (subset : Set (baseChangeScheme f V)) ⊆ ambient
  /-- `Z` is closed in the ambient open. -/
  isClosed_in_ambient :
    IsClosed (ambient.ι ⁻¹' (subset : Set (baseChangeScheme f V)))
  /-- The reduced induced scheme of `Z` is finite over `V`. -/
  [toBase_isFinite :
    IsFinite (LocallyClosedReduction.ι subset ≫ baseChangeToBase f V)]

/-- A finite reduced support presentation determines a canonical finite-support index. -/
def AdmissiblePresentation.toIndex {V : Y.Etale} (A : AdmissiblePresentation f V) :
    FiniteSupportColimit.Index f V :=
  ⟨(A.subset, OrderDual.toDual A.ambient),
    ⟨⟨LocallyClosedReduction.scheme A.subset, LocallyClosedReduction.ι A.subset,
      inferInstance, A.toBase_isFinite, LocallyClosedReduction.range_ι A.subset⟩,
      A.subset_le_ambient, A.isClosed_in_ambient⟩⟩

/-- Finite reduced support presentations ordered through their canonical support indices. -/
abbrev Admissible (V : Y.Etale) :=
  Order.Induced (AdmissiblePresentation.toIndex f (V := V))

/-- Eligibility of a locally closed support is equivalent to finiteness of its reduced
induced scheme over the base. -/
theorem eligible_iff_isFinite (V : Y.Etale)
    (Z : LocallyCloseds (baseChangeScheme f V)) :
    FiniteSupportColimit.Eligible f V Z ↔
      IsFinite (LocallyClosedReduction.ι Z ≫ baseChangeToBase f V) :=
  sorry

/-- Recover the reduced support presentation from a canonical finite-support index. -/
def Admissible.ofIndex {V : Y.Etale} (A : FiniteSupportColimit.Index f V) :
    Admissible f V where
  subset := A.subset
  ambient := A.ambient
  subset_le_ambient := A.subset_le_ambient
  isClosed_in_ambient := A.isClosed_in_ambient
  toBase_isFinite := (eligible_iff_isFinite f V A.subset).mp A.spec.1

/-- Reduced support presentations and canonical finite-support indices have the same data. -/
def Admissible.toIndexEquiv (V : Y.Etale) :
    Admissible f V ≃ FiniteSupportColimit.Index f V where
  toFun := AdmissiblePresentation.toIndex f
  invFun := Admissible.ofIndex f
  left_inv A := by cases A; rfl
  right_inv A := by cases A; rfl

/-- The functor sending a reduced support presentation to its canonical index. -/
def Admissible.toIndexFunctor (V : Y.Etale) :
    Admissible f V ⥤ FiniteSupportColimit.Index f V where
  obj := AdmissiblePresentation.toIndex f
  map h := CategoryTheory.homOfLE (leOfHom h)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Build an admissible support from a locally closed subset finite over `V` and
an ambient open in which it is closed. -/
def Admissible.of {V : Y.Etale} (Z : LocallyCloseds (baseChangeScheme f V))
    (U : (baseChangeScheme f V).Opens)
    (h_subset : (Z : Set (baseChangeScheme f V)) ⊆ U)
    (h_closed : IsClosed (U.ι ⁻¹' (Z : Set (baseChangeScheme f V))))
    [IsFinite (LocallyClosedReduction.ι Z ≫ baseChangeToBase f V)] :
    Admissible f V where
  subset := Z
  ambient := U
  subset_le_ambient := h_subset
  isClosed_in_ambient := h_closed
  toBase_isFinite := inferInstance

/-- The smart constructor records the given locally closed subset and ambient
open. -/
theorem Admissible.of_subset {V : Y.Etale} (Z : LocallyCloseds (baseChangeScheme f V))
    (U : (baseChangeScheme f V).Opens)
    (h_subset : (Z : Set (baseChangeScheme f V)) ⊆ U)
    (h_closed : IsClosed (U.ι ⁻¹' (Z : Set (baseChangeScheme f V))))
    [IsFinite (LocallyClosedReduction.ι Z ≫ baseChangeToBase f V)] :
    (Admissible.of f Z U h_subset h_closed).subset = Z ∧
      (Admissible.of f Z U h_subset h_closed).ambient = U :=
  ⟨rfl, rfl⟩

/-- An admissible support records a locally closed subset of `|X_V|` finite over
`V` and closed in the chosen ambient open. -/
theorem Admissible.spec {V : Y.Etale} (A : Admissible f V) :
    (A.subset : Set (baseChangeScheme f V)) ⊆ A.ambient ∧
      IsClosed (A.ambient.ι ⁻¹' (A.subset : Set (baseChangeScheme f V))) ∧
      IsFinite (LocallyClosedReduction.ι A.subset ≫ baseChangeToBase f V) :=
  ⟨A.subset_le_ambient, A.isClosed_in_ambient, A.toBase_isFinite⟩

/-- A locally closed subset is contained in its coborder ambient open. -/
theorem subset_le_ambientOpen {W : Scheme.{u}} (Z : LocallyCloseds W) :
    (Z : Set W) ⊆ LocallyClosedReduction.ambientOpen Z :=
  subset_coborder

/-- A locally closed subset is closed in its coborder ambient open. -/
theorem isClosed_in_ambientOpen {W : Scheme.{u}} (Z : LocallyCloseds W) :
    IsClosed ((LocallyClosedReduction.ambientOpen Z).ι ⁻¹' (Z : Set W)) :=
  isClosed_preimage_val_coborder

/-- The admissible support with coborder ambient open. -/
def Admissible.ofSubset {V : Y.Etale} (Z : LocallyCloseds (baseChangeScheme f V))
    [IsFinite (LocallyClosedReduction.ι Z ≫ baseChangeToBase f V)] :
    Admissible f V :=
  Admissible.of f Z (LocallyClosedReduction.ambientOpen Z)
    (subset_le_ambientOpen Z) (isClosed_in_ambientOpen Z)

/-- The coborder presentation uses the given locally closed subset and its
ambient open. -/
theorem Admissible.ofSubset_spec {V : Y.Etale}
    (Z : LocallyCloseds (baseChangeScheme f V))
    [IsFinite (LocallyClosedReduction.ι Z ≫ baseChangeToBase f V)] :
    (Admissible.ofSubset f Z).subset = Z ∧
      (Admissible.ofSubset f Z).ambient = LocallyClosedReduction.ambientOpen Z :=
  ⟨rfl, rfl⟩

/-- The admissible support associated to a finite-support pair `(Z, s)`. -/
def Admissible.ofTerm {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    {V : Y.Etale} (t : FiniteSupportTerm f F V) : Admissible f V :=
  Admissible.ofIndex f (FiniteSupportColimit.Index.ofTerm t)

/-- The admissible support of a finite-support pair records its locally closed
subset and ambient open. -/
theorem Admissible.ofTerm_subset {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    {V : Y.Etale} (t : FiniteSupportTerm f F V) :
    (Admissible.ofTerm f t).subset = t.locallyClosedSubset ∧
      (Admissible.ofTerm f t).ambient = t.ambient :=
  ⟨rfl, rfl⟩

/-- The preorder on admissible supports is subset inclusion of supports and
reverse inclusion of ambient opens. -/
theorem Admissible.le_iff {V : Y.Etale} (A B : Admissible f V) :
    A ≤ B ↔
      (A.subset : Set (baseChangeScheme f V)) ⊆ B.subset ∧ B.ambient ≤ A.ambient :=
  Iff.rfl

/-- The scheme morphism `X_{V'} ⟶ X_V` induced by a morphism of étale
`Y`-schemes. -/
def baseChangeSchemeMap {V' V : Y.Etale} (g : V' ⟶ V) :
    baseChangeScheme f V' ⟶ baseChangeScheme f V :=
  ((smallEtalePullback f).map g).left

/-- Base change of étale `Y`-schemes acts on `X_V` by the underlying morphism of
`smallEtalePullback`. -/
theorem baseChangeSchemeMap_eq {V' V : Y.Etale} (g : V' ⟶ V) :
    baseChangeSchemeMap f g = ((smallEtalePullback f).map g).left :=
  rfl

/-- Inverse image of an admissible support along `X_{V'} ⟶ X_V`. -/
def Admissible.pullback {V' V : Y.Etale} (g : V' ⟶ V) (A : Admissible f V) :
    Admissible f V' where
  subset := ⟨baseChangeSchemeMap f g ⁻¹' A.subset, sorry⟩
  ambient := baseChangeSchemeMap f g ⁻¹ᵁ A.ambient
  subset_le_ambient := sorry
  isClosed_in_ambient := sorry
  toBase_isFinite := sorry

/-- Pullback of admissible supports is monotone. -/
theorem Admissible.pullback_mono {V' V : Y.Etale} (g : V' ⟶ V)
    {A B : Admissible f V} (h : A ≤ B) :
    Admissible.pullback f g A ≤ Admissible.pullback f g B :=
  sorry

/-- The functor on admissible supports induced by inverse image along
`X_{V'} ⟶ X_V`. -/
def Admissible.pullbackFunctor {V' V : Y.Etale} (g : V' ⟶ V) :
    Admissible f V ⥤ Admissible f V' where
  obj := Admissible.pullback f g
  map h := homOfLE (Admissible.pullback_mono f g (leOfHom h))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The pullback functor acts by inverse image of admissible supports. -/
theorem Admissible.pullbackFunctor_obj {V' V : Y.Etale} (g : V' ⟶ V)
    (A : Admissible f V) :
    (Admissible.pullbackFunctor f g).obj A = Admissible.pullback f g A :=
  rfl

end FiniteSupport
end AlgebraicGeometry.Scheme.Etale

end
