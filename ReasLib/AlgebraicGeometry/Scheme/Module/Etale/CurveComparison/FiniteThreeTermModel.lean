/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteContinuousSpan
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.Single

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open scoped ZeroObject
noncomputable section
universe u v

namespace FiniteThreeTermModel
variable (R : Type u) [Ring R] [Finite R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable (S : ShortComplex (DiscreteModuleCat R G))

/-- Concrete bottom cohomology of the three-term truncation. -/
abbrev H0 := LinearMap.ker S.f.hom.hom.hom

/-- Concrete top cohomology of the three-term truncation. -/
abbrev H2 := S.X₃.obj.V ⧸ LinearMap.range S.g.hom.hom.hom

/-- The actual first differential with codomain restricted to cycles. -/
def toCycles : S.X₁.obj.V →ₗ[R] LinearMap.ker S.g.hom.hom.hom :=
  LinearMap.codRestrict _ S.f.hom.hom.hom (by sorry)

/-- Concrete middle cohomology, with quotient representatives available. -/
abbrev H1 := (LinearMap.ker S.g.hom.hom.hom) ⧸ LinearMap.range (toCycles R G S)

/-- Start with actual representatives of all top cohomology classes. -/
def topGenerators : Set S.X₃.obj.V := Set.range (fun z : H2 R G S ↦ Quotient.out z)

/-- The top representative has exactly the prescribed cohomology class. -/
theorem topRepresentative_spec (z : H2 R G S) :
    (LinearMap.range S.g.hom.hom.hom).mkQ (Quotient.out z) = z := Quotient.out_eq z

/-- The top finite stage is its explicit invariant span. -/
abbrev top := FiniteContinuousSpan.span R G S.X₃ (topGenerators R G S)

/-- The finite top stage vectors that are genuine boundaries in S. -/
abbrev TopBoundary := {x : top R G S // x.val ∈ LinearMap.range S.g.hom.hom.hom}

/-- Choose preimages ONLY of specified boundary vectors. -/
def topLift (x : TopBoundary R G S) : S.X₂.obj.V := Classical.choose x.property

/-- This is the specification of the selected boundary preimage. -/
theorem topLift_spec (x : TopBoundary R G S) :
    S.g.hom.hom.hom (topLift R G S x) = x.val.val := Classical.choose_spec x.property

/-- Add middle cohomology representatives and lifts of all top boundary relations. -/
def middleGenerators : Set S.X₂.obj.V :=
  Set.range (topLift R G S) ∪ Set.range (fun z : H1 R G S ↦ (Quotient.out z).val)

/-- The selected middle cycle represents exactly its given quotient class. -/
theorem middleRepresentative_spec (z : H1 R G S) :
    (LinearMap.range (toCycles R G S)).mkQ (Quotient.out z) = z := Quotient.out_eq z

/-- The actual invariant middle stage. -/
abbrev middle := FiniteContinuousSpan.span R G S.X₂ (middleGenerators R G S)

/-- The middle-stage vectors that are genuine boundaries in S. -/
abbrev MiddleBoundary := {x : middle R G S // x.val ∈ LinearMap.range S.f.hom.hom.hom}

/-- Choose preimages of exactly those middle boundary vectors. -/
def middleLift (x : MiddleBoundary R G S) : S.X₁.obj.V := Classical.choose x.property

/-- Specification of the chosen middle boundary lift. -/
theorem middleLift_spec (x : MiddleBoundary R G S) :
    S.f.hom.hom.hom (middleLift R G S x) = x.val.val := Classical.choose_spec x.property

/-- Finish with these boundary lifts and all bottom cohomology vectors. -/
def bottomGenerators : Set S.X₁.obj.V :=
  Set.range (middleLift R G S) ∪ Set.range (fun z : H0 R G S ↦ z.val)

/-- The actual invariant bottom stage. -/
abbrev bottom := FiniteContinuousSpan.span R G S.X₁ (bottomGenerators R G S)

/-- The differentials preserve the specified finite-stage choices by construction. -/
theorem middle_maps_top : middle R G S ≤ (top R G S).comap S.g.hom.hom.hom := by sorry

/-- Every bottom generator maps to the middle stage. -/
theorem bottom_maps_middle : bottom R G S ≤ (middle R G S).comap S.f.hom.hom.hom := by sorry

/-- The actual subcomplex differentials are restrictions of the original maps. -/
def model : ShortComplex (DiscreteModuleCat R G) where
  X₁ := FiniteContinuousSpan.obj R G S.X₁ (bottomGenerators R G S)
  X₂ := FiniteContinuousSpan.obj R G S.X₂ (middleGenerators R G S)
  X₃ := FiniteContinuousSpan.obj R G S.X₃ (topGenerators R G S)
  f := ObjectProperty.homMk
    { hom := ModuleCat.ofHom (LinearMap.codRestrict (middle R G S)
        (S.f.hom.hom.hom.domRestrict (bottom R G S))
        (fun x ↦ bottom_maps_middle R G S x.property))
      comm := fun _ ↦ by sorry }
  g := ObjectProperty.homMk
    { hom := ModuleCat.ofHom (LinearMap.codRestrict (top R G S)
        (S.g.hom.hom.hom.domRestrict (middle R G S))
        (fun x ↦ middle_maps_top R G S x.property))
      comm := fun _ ↦ by sorry }
  zero := by sorry

/-- Inclusion uses the original subtype maps in each degree. -/
def inclusion : model R G S ⟶ S where
  τ₁ := FiniteContinuousSpan.inclusion R G S.X₁ (bottomGenerators R G S)
  τ₂ := FiniteContinuousSpan.inclusion R G S.X₂ (middleGenerators R G S)
  τ₃ := FiniteContinuousSpan.inclusion R G S.X₃ (topGenerators R G S)
  comm₁₂ := by sorry
  comm₂₃ := by sorry

instance top_finite [Finite (H2 R G S)] : Finite (top R G S) :=
  FiniteContinuousSpan.finite R G S.X₃ _ (Set.finite_range _)

instance middle_finite [Finite (H2 R G S)] [Finite (H1 R G S)] : Finite (middle R G S) :=
  FiniteContinuousSpan.finite R G S.X₂ _ ((Set.finite_range _).union (Set.finite_range _))

instance bottom_finite [Finite (H2 R G S)] [Finite (H1 R G S)] [Finite (H0 R G S)] :
    Finite (bottom R G S) :=
  FiniteContinuousSpan.finite R G S.X₁ _ ((Set.finite_range _).union (Set.finite_range _))

/-- Realize this short complex in degrees 0,1,2 with genuine zero extension. -/
def terms : ℕ → DiscreteModuleCat R G
  | 0 => S.X₁
  | 1 => S.X₂
  | 2 => S.X₃
  | _ + 3 => 0

/-- The only nonzero differentials are the original two maps. -/
def differential : ∀ n : ℕ, terms R G S n ⟶ terms R G S (n + 1)
  | 0 => S.f
  | 1 => S.g
  | _ + 2 => 0

/-- The actual differential squares to zero. -/
theorem differential_squared (n : ℕ) :
    differential R G S n ≫ differential R G S (n + 1) = 0 := by sorry

/-- A concrete nonnegative cochain complex, rather than a cohomology-object substitute. -/
def cochain := CochainComplex.of (terms R G S) (differential R G S) (differential_squared R G S)

/-- The finite-model comparison consists only of the specified inclusions. -/
def cochainInclusion : cochain R G (model R G S) ⟶ cochain R G S :=
  CochainComplex.ofHom
    (fun n ↦ match n with
      | 0 => (inclusion R G S).τ₁
      | 1 => (inclusion R G S).τ₂
      | 2 => (inclusion R G S).τ₃
      | _ + 3 => 0) (by sorry)

/-- The representatives give surjectivity and the chosen boundary lifts give
injectivity in all three degrees. No projectivity of finite representations is used. -/
theorem cochainInclusion_quasiIso : QuasiIso (cochainInclusion R G S) := by sorry

/-- Finiteness is conditional on finite cohomology of the given truncation,
not a universal finiteness or projectivity claim about arbitrary representations. -/
theorem finite_model_terms [Finite (H2 R G S)] [Finite (H1 R G S)] [Finite (H0 R G S)]
    (n : ℕ) : Finite ((cochain R G (model R G S)).X n).obj.V := by sorry

end FiniteThreeTermModel
