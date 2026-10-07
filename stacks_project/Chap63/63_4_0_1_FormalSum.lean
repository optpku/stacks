module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.GroupTheory.FreeAbelianGroup
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import stacks_project.Chap63.«63_4_0_1_SectionsSupportedIn»

/-!
# Finite formal sums of étale sections with finite support

Admissible pairs `(Z, s)` on a base change `X_V`, and the free abelian group of
finite formal sums of such pairs, before imposing the later relations.
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

/-- The projection `X_V ⟶ V`, given by `pullback.fst V.hom f`. -/
abbrev baseChangeToBase : baseChangeScheme f V ⟶ V.left :=
  pullback.fst V.hom f

/-- The structure morphism `X_V ⟶ X` of the small-étale pullback of `V`. -/
abbrev baseChangeToSource : baseChangeScheme f V ⟶ X :=
  ((smallEtalePullback f).obj V).hom

/-- An admissible pair `(Z, s)`: a locally closed subscheme of `X_V` finite over
`V`, together with a section of `F` on an open of `X_V` containing `Z` as a
closed subscheme, supported in `Z`. -/
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
  /-- The section `s ∈ F(U)` on the ambient open. -/
  sec : F.1.obj (op (Scheme.Etale.mk (ambient.ι ≫ baseChangeToSource f V)))
  /-- The section lies in `H_Z(F)`. -/
  mem_sectionsSupportedIn :
    sec ∈ sectionsSupportedIn F (baseChangeToSource f V)
      ⟨Set.range ι, ι_isImmersion.isLocallyClosed_range⟩ ambient
      range_subset_ambient isClosed_in_ambient

/-- Construct an admissible pair from a locally closed immersion finite over `V`,
an ambient open containing the image as a closed subscheme, and a section of `F`
supported in that image. -/
def FiniteSupportTerm.of (Z : Scheme.{u}) (ι : Z ⟶ baseChangeScheme f V)
    [IsImmersion ι] [IsFinite (ι ≫ baseChangeToBase f V)]
    (U : (baseChangeScheme f V).Opens) (h_subset : Set.range ι ⊆ U)
    (h_closed : IsClosed (U.ι ⁻¹' Set.range ι))
    (s : F.1.obj (op (Scheme.Etale.mk (U.ι ≫ baseChangeToSource f V))))
    (h_mem : s ∈ sectionsSupportedIn F (baseChangeToSource f V)
      ⟨Set.range ι, ι.isLocallyClosed_range⟩ U h_subset
      h_closed) :
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

/-- An admissible pair records a locally closed subscheme of `X_V` contained as a
closed subscheme of the chosen ambient open, together with a section in `H_Z(F)`. -/
theorem FiniteSupportTerm.spec (t : FiniteSupportTerm f F V) :
    Set.range t.ι ⊆ t.ambient ∧
      IsClosed (t.ambient.ι ⁻¹' Set.range t.ι) ∧
      t.sec ∈ sectionsSupportedIn F (baseChangeToSource f V) t.locallyClosedSubset
        t.ambient t.range_subset_ambient t.isClosed_in_ambient :=
  sorry

/-- The group of finite formal sums of admissible pairs `(Z, s)` on `X_V`. -/
abbrev FiniteSupportFormalSum : Type (u + 1) :=
  FreeAbelianGroup (FiniteSupportTerm f F V)

variable {f F V}

namespace FiniteSupportFormalSum

/-- The finite formal sum of an indexed family of admissible pairs. -/
def sum {n : ℕ} (t : Fin n → FiniteSupportTerm f F V) :
    FiniteSupportFormalSum f F V :=
  ∑ i, FreeAbelianGroup.of (t i)

end FiniteSupportFormalSum

end AlgebraicGeometry.Scheme.Etale

end
