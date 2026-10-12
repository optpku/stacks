/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Admissible
public import ReasLib.Algebra.Category.DifferentialGraded.Shift
public import Mathlib.CategoryTheory.Shift.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Admissible cones in differential graded categories

A compatible enriched shift canonically turns the formula `π d s` of a graded splitting into a
boundary morphism.  The API retains `CompBoundaryAssignment` as an explicit replacement point,
while `AdmissibleBoundary.assignment` supplies the canonical value used by ordinary downstream
code.  A cone chosen for every morphism remains observable data.
-/

open CategoryTheory

universe u v w

namespace DifferentialGradedCategory

variable {R : Type u} [CommRing R]
variable {A : Type v} [D : DifferentialGradedCategory.{u, v, w} R A]
variable [HasShift (Comp R A) ℤ]

/-- An explicit choice of boundary morphism for every split short complex in `Comp R A`. -/
@[stacks 09QJ "boundary assignment for admissible cones"]
structure CompBoundaryAssignment
    (R : Type u) [CommRing R]
    (A : Type v) [DifferentialGradedCategory.{u, v, w} R A]
    [HasShift (Comp R A) ℤ] : Type (max u v w + 1) where
  /-- The boundary morphism associated to a chosen splitting. -/
  boundary {S : ShortComplex (Comp R A)} (σ : S.GradedSplitting) :
    S.X₃ ⟶ S.X₁⟦(1 : ℤ)⟧
  /-- Boundary morphisms obtained from two graded splittings are homotopic. -/
  boundary_homotopic {S : ShortComplex (Comp R A)} (σ τ : S.GradedSplitting) :
    Homotopic S.X₃.obj (S.X₁⟦(1 : ℤ)⟧).obj (boundary σ) (boundary τ)

namespace CompBoundaryAssignment

/-- The boundary morphism of an explicitly displayed split short complex. -/
abbrev boundaryMk (B : CompBoundaryAssignment R A)
    {x y z : Comp R A} {f : x ⟶ y} {g : y ⟶ z}
    (zero : f ≫ g = 0) (σ : (ShortComplex.mk f g zero).GradedSplitting) :
    z ⟶ x⟦(1 : ℤ)⟧ :=
  B.boundary σ

/-- A cone on `f : x ⟶ y` compatible with the explicit boundary assignment `B`. -/
@[stacks 09QJ "admissible cone in a differential graded category"]
structure AdmissibleCone (B : CompBoundaryAssignment R A)
    {x y : Comp R A} (f : x ⟶ y) : Type (max u v w) where
  /-- The cone object. -/
  obj : Comp R A
  /-- The map from the target into the cone. -/
  toCone : y ⟶ obj
  /-- The map from the cone into the shifted source. -/
  toShift : obj ⟶ x⟦(1 : ℤ)⟧
  /-- Consecutive maps in the cone sequence compose to zero. -/
  toCone_toShift : toCone ≫ toShift = 0
  /-- A splitting of the cone short complex after forgetting closedness. -/
  splitting : (ShortComplex.mk toCone toShift toCone_toShift).GradedSplitting
  /-- The boundary of the split cone sequence is the shift of `f`. -/
  boundary_eq : B.boundary splitting = f⟦(1 : ℤ)⟧'

namespace AdmissibleCone

variable {B : CompBoundaryAssignment R A}
variable {x y : Comp R A} {f : x ⟶ y}

/-- The short complex underlying an admissible cone. -/
abbrev shortComplex (C : B.AdmissibleCone f) : ShortComplex (Comp R A) :=
  ShortComplex.mk C.toCone C.toShift C.toCone_toShift

/-- The first map of the short complex underlying an admissible cone. -/
@[simp] theorem shortComplex_f (C : B.AdmissibleCone f) :
    C.shortComplex.f = C.toCone := sorry

/-- The second map of the short complex underlying an admissible cone. -/
@[simp] theorem shortComplex_g (C : B.AdmissibleCone f) :
    C.shortComplex.g = C.toShift := sorry

end AdmissibleCone

/-- Situation 22.27.2 (09QJ): an explicit compatible choice of an admissible cone for every
morphism in `Comp R A`. -/
@[stacks 09QJ]
structure AdmissibleCones (B : CompBoundaryAssignment R A) : Type (max u v w + 1) where
  /-- The chosen admissible cone on a morphism. -/
  cone {x y : Comp R A} (f : x ⟶ y) : B.AdmissibleCone f

namespace AdmissibleCones

variable {B : CompBoundaryAssignment R A}

/-- The short complex underlying the cone chosen for `f`. -/
abbrev shortComplex (C : B.AdmissibleCones)
    {x y : Comp R A} (f : x ⟶ y) : ShortComplex (Comp R A) :=
  (C.cone f).shortComplex

/-- The splitting of the short complex underlying the cone chosen for `f`. -/
abbrev splitting (C : B.AdmissibleCones)
    {x y : Comp R A} (f : x ⟶ y) : (C.shortComplex f).GradedSplitting :=
  (C.cone f).splitting

/-- Lemma 22.27.10 (09QR): the chosen cone short complex has boundary equal to the shift of
its defining morphism. -/
@[simp, stacks 09QR] theorem boundary_eq (C : B.AdmissibleCones)
    {x y : Comp R A} (f : x ⟶ y) :
    B.boundary (C.splitting f) = f⟦(1 : ℤ)⟧' := sorry

/-- The first map of the chosen cone short complex is its map into the cone. -/
@[simp] theorem shortComplex_f (C : B.AdmissibleCones)
    {x y : Comp R A} (f : x ⟶ y) :
    (C.shortComplex f).f = (C.cone f).toCone := sorry

/-- The second map of the chosen cone short complex is its map into the shift. -/
@[simp] theorem shortComplex_g (C : B.AdmissibleCones)
    {x y : Comp R A} (f : x ⟶ y) :
    (C.shortComplex f).g = (C.cone f).toShift := sorry

end AdmissibleCones

end CompBoundaryAssignment

namespace AdmissibleBoundary

/-- The degree-one homogeneous boundary `π d s` associated to a graded splitting. -/
def raw {S : ShortComplex (Comp R A)} (σ : S.GradedSplitting) :
    S.X₃.obj ⟶[(1 : ℤ)] S.X₁.obj :=
  castHom (add_zero (1 : ℤ))
    (D.comp σ.r (D.d 0 σ.s))

/-- The boundary formula can equivalently be written as `-d(π) s`. -/
theorem raw_eq_negDifferential {S : ShortComplex (Comp R A)} (σ : S.GradedSplitting) :
    raw σ = -castHom (zero_add (1 : ℤ))
      (D.comp (D.d 0 σ.r) σ.s) := sorry

/-- The homogeneous boundary `π d s` is a cycle. -/
theorem raw_closed {S : ShortComplex (Comp R A)} (σ : S.GradedSplitting) :
    D.d 1 (raw σ) = 0 := sorry

variable [ShiftCompatibility R A]

/-- The canonical connecting morphism of a graded-split short complex. -/
@[stacks 09P6 "connecting morphism of a graded-split DG sequence"]
def boundary {S : ShortComplex (Comp R A)} (σ : S.GradedSplitting) :
    S.X₃ ⟶ S.X₁⟦(1 : ℤ)⟧ :=
  ShiftCompatibility.cycleToShift S.X₃ S.X₁ 1 (raw σ) (raw_closed σ)

/-- The homogeneous representative of the canonical connecting morphism is the shifted form of
`π d s`. -/
@[simp]
theorem boundary_val {S : ShortComplex (Comp R A)} (σ : S.GradedSplitting) :
    (boundary σ).val = ShiftCompatibility.toShiftLinear S.X₃ S.X₁ 1 (raw σ) := sorry

/-- Connecting morphisms obtained from two graded splittings are homotopic. -/
theorem boundary_homotopic {S : ShortComplex (Comp R A)} (σ τ : S.GradedSplitting) :
    Homotopic S.X₃.obj (S.X₁⟦(1 : ℤ)⟧).obj (boundary σ) (boundary τ) := sorry

/-- The second short-complex map followed by the connecting morphism is null-homotopic. -/
theorem g_boundary_homotopic {S : ShortComplex (Comp R A)} (σ : S.GradedSplitting) :
    Homotopic S.X₂.obj (S.X₁⟦(1 : ℤ)⟧).obj (S.g ≫ boundary σ) 0 := sorry

/-- The connecting morphism followed by the shifted first map is null-homotopic. -/
theorem boundary_shift_f_homotopic {S : ShortComplex (Comp R A)} (σ : S.GradedSplitting) :
    Homotopic S.X₃.obj (S.X₂⟦(1 : ℤ)⟧).obj
      (boundary σ ≫ S.f⟦(1 : ℤ)⟧') 0 := sorry

/-- The canonical boundary assignment determined by the compatible enriched shift. -/
@[stacks 09P6 "canonical boundary assignment from compatible DG shifts"]
def assignment : CompBoundaryAssignment R A where
  boundary := boundary
  boundary_homotopic := boundary_homotopic

/-- An admissible cone using the canonical boundary assignment. -/
abbrev Cone {x y : Comp R A} (f : x ⟶ y) : Type (max u v w) :=
  (assignment (R := R) (A := A)).AdmissibleCone f

/-- A choice of admissible cone for every morphism, using the canonical boundary assignment. -/
@[stacks 09QJ "canonical admissible-cone system"]
abbrev ConeSystem : Type (max u v w + 1) :=
  (assignment (R := R) (A := A)).AdmissibleCones

namespace ConeSystem

/-- The boundary of every cone in a canonical cone system is the shifted defining map. -/
@[simp]
theorem boundary_eq (C : ConeSystem (R := R) (A := A))
    {x y : Comp R A} (f : x ⟶ y) :
    boundary (C.splitting f) = f⟦(1 : ℤ)⟧' := sorry

end ConeSystem

end AdmissibleBoundary

end DifferentialGradedCategory
