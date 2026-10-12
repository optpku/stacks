/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.GroupTheory.FreeAbelianGroup
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SectionsSupportedIn
public import ReasLib.Topology.LocallyClosed.Subsets

/-!
# Finite-support formal sums on an étale base change

Admissible pairs consist of a locally closed subscheme finite over an étale
base change together with a section supported on that locally closed subset.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open TopologicalSpace
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
variable (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)

/-- The base change scheme `X_V = X ×_Y V`. -/
abbrev baseChangeScheme : Scheme.{u} :=
  ((smallEtalePullback f).obj V).left

/-- The projection `X_V ⟶ V` from the small-étale base change. -/
abbrev baseChangeToBase : baseChangeScheme f V ⟶ V.left :=
  pullback.fst V.hom f

/-- The structure morphism `X_V ⟶ X` from the small-étale base change. -/
abbrev baseChangeToSource : baseChangeScheme f V ⟶ X :=
  ((smallEtalePullback f).obj V).hom

/-- Sections on an ambient open whose support lies in a locally closed subset. -/
def sectionsSupportedIn {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {W : Scheme.{u}}
    (hW : W ⟶ X) [Etale hW] (Z : LocallyCloseds W) (U : W.Opens)
    (h_subset : (Z : Set W) ⊆ U)
    (h_closed : IsClosed (U.ι ⁻¹' (Z : Set W))) :
    AddSubgroup (F.1.obj (op (Scheme.Etale.mk (U.ι ≫ hW)))) :=
  abelianSheafSectionsSupportedIn F (Scheme.Etale.mk (U.ι ≫ hW))
    (U.ι ⁻¹' (Z : Set W))

/-- Membership is equivalent to containment of the section-support image in the
locally closed subset. -/
theorem mem_sectionsSupportedIn_iff {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {W : Scheme.{u}}
    (hW : W ⟶ X) [Etale hW] (Z : LocallyCloseds W) (U : W.Opens)
    (h_subset : (Z : Set W) ⊆ U)
    (h_closed : IsClosed (U.ι ⁻¹' (Z : Set W)))
    (σ : F.1.obj (op (Scheme.Etale.mk (U.ι ≫ hW)))) :
    σ ∈ sectionsSupportedIn F hW Z U h_subset h_closed ↔
      U.ι '' (abelianSheafSectionSupport F (Scheme.Etale.mk (U.ι ≫ hW)) σ :
        Set (Scheme.Etale.mk (U.ι ≫ hW)).left) ⊆ (Z : Set W) :=
  sorry

/-- An admissible pair of finite support on `X_V`. -/
structure FiniteSupportTerm where
  /-- The locally closed subscheme `Z ⊂ X_V`. -/
  subscheme : Scheme.{u}
  /-- The locally closed immersion `Z ⟶ X_V`. -/
  ι : subscheme ⟶ baseChangeScheme f V
  [ι_isImmersion : IsImmersion ι]
  [toBase_isFinite : IsFinite (ι ≫ baseChangeToBase f V)]
  /-- An open of `X_V` containing `Z` as a closed subscheme. -/
  ambient : (baseChangeScheme f V).Opens
  /-- The image of `Z` is contained in the ambient open. -/
  range_subset_ambient : Set.range ι ⊆ ambient
  /-- `Z` is closed in the ambient open. -/
  isClosed_in_ambient : IsClosed (ambient.ι ⁻¹' Set.range ι)
  /-- The section on the ambient open. -/
  sec : F.1.obj (op (Scheme.Etale.mk (ambient.ι ≫ baseChangeToSource f V)))
  /-- The section is supported on the locally closed image of `Z`. -/
  mem_sectionsSupportedIn :
    sec ∈ sectionsSupportedIn F (baseChangeToSource f V)
      ⟨Set.range ι, ι_isImmersion.isLocallyClosed_range⟩ ambient
      range_subset_ambient isClosed_in_ambient

/-- Construct an admissible pair from its explicit geometric and section data. -/
def FiniteSupportTerm.of (Z : Scheme.{u}) (ι : Z ⟶ baseChangeScheme f V)
    [IsImmersion ι] [IsFinite (ι ≫ baseChangeToBase f V)]
    (U : (baseChangeScheme f V).Opens) (h_subset : Set.range ι ⊆ U)
    (h_closed : IsClosed (U.ι ⁻¹' Set.range ι))
    (s : F.1.obj (op (Scheme.Etale.mk (U.ι ≫ baseChangeToSource f V))))
    (h_mem : s ∈ sectionsSupportedIn F (baseChangeToSource f V)
      ⟨Set.range ι, ι.isLocallyClosed_range⟩ U h_subset h_closed) :
    FiniteSupportTerm f F V where
  subscheme := Z
  ι := ι
  ambient := U
  range_subset_ambient := h_subset
  isClosed_in_ambient := h_closed
  sec := s
  mem_sectionsSupportedIn := h_mem

/-- The locally closed subset of `X_V` cut out by an admissible pair. -/
def FiniteSupportTerm.locallyClosedSubset (t : FiniteSupportTerm f F V) :
    LocallyCloseds (baseChangeScheme f V) :=
  ⟨Set.range t.ι, t.ι_isImmersion.isLocallyClosed_range⟩

/-- An admissible pair satisfies its range, closedness, and support conditions. -/
theorem FiniteSupportTerm.spec (t : FiniteSupportTerm f F V) :
    Set.range t.ι ⊆ t.ambient ∧
      IsClosed (t.ambient.ι ⁻¹' Set.range t.ι) ∧
      t.sec ∈ sectionsSupportedIn F (baseChangeToSource f V) t.locallyClosedSubset
        t.ambient t.range_subset_ambient t.isClosed_in_ambient :=
  sorry

/-- The free abelian group of finite formal sums of admissible pairs. -/
abbrev FiniteSupportFormalSum : Type (u + 1) :=
  FreeAbelianGroup (FiniteSupportTerm f F V)

variable {f F V}

namespace FiniteSupportFormalSum

/-- The formal sum associated to a finite indexed family of admissible pairs. -/
def sum {n : ℕ} (t : Fin n → FiniteSupportTerm f F V) :
    FiniteSupportFormalSum f F V :=
  ∑ i, FreeAbelianGroup.of (t i)

end FiniteSupportFormalSum

end AlgebraicGeometry.Scheme.Etale

end
