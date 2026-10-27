/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Limits.Coproduct

/-!
# Private proposal: explicit free DG cells and a single attachment

No resolution or cover is selected from an existence proposition. A cell of degree `s`
is the shifted regular module `A[-s]`. All carriers are small in `v`, independently of `u`.
The only admitted fields below are equations for the displayed data.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace DifferentialGradedModule.PropertyP.PrivateConstruction

variable {R : Type u} [CommRing R] {A : CochainDGAlgebra.{u, v} R}

/-- A homogeneous family of free DG cells, with its actual direct-sum carrier. -/
abbrev freeCells {I : Type v} (s : I → ℤ) : DifferentialGradedModule.{u, v} A :=
  Coproduct.obj (fun i ↦ DifferentialGradedModule.shift A.regularModule (-s i))

/-- The presentation of the free piece uses both explicit arrows of the concrete coproduct
comparison; it does not select an inverse from an `IsIso` assertion. -/
def freePiece {I : Type v} (s : I → ℤ) : Piece A (freeCells (A := A) s) where
  index := I
  degree := fun i ↦ -s i
  iso := (Coproduct.iso (fun i ↦ DifferentialGradedModule.shift A.regularModule (-s i))).symm

/-- Inclusion of a coefficient into its specified free cell. -/
def cellCoeff {I : Type v} (s : I → ℤ) (n : ℤ) (i : I) :
    A.X (n + -s i) →ₗ[R] (freeCells (A := A) s).X n :=
  Coproduct.injectionLinearMap
    (fun j ↦ DifferentialGradedModule.shift A.regularModule (-s j)) i n

/-- Send a free cell to a prescribed homogeneous element, without asserting it is closed. -/
def evaluationSummand {I : Type v} (s : I → ℤ)
    (M : DifferentialGradedModule.{u, v} A) (z : ∀ i, M.X (s i))
    (n : ℤ) (i : I) : A.X (n + -s i) →ₗ[R] M.X n :=
  ModuleCat.castLinearMap (congrArg M.X (by omega)) (M.smul (s i) (n + -s i) (z i))

/-- The actual linear extension of the prescribed generator images. -/
def evaluation {I : Type v} (s : I → ℤ)
    (M : DifferentialGradedModule.{u, v} A) (z : ∀ i, M.X (s i)) (n : ℤ) :
    (freeCells (A := A) s).X n →ₗ[R] M.X n := by
  classical
  exact DirectSum.toModule R I _ (evaluationSummand s M z n)

/-- Change the labels of free cells, preserving their degrees. -/
def reindexLinear {I J : Type v} (s : I → ℤ) (t : J → ℤ)
    (h : I → J) (hs : ∀ i, s i = t (h i)) (n : ℤ) :
    (freeCells (A := A) s).X n →ₗ[R] (freeCells (A := A) t).X n := by
  classical
  exact DirectSum.toModule R I _ (fun i ↦
    (cellCoeff t n (h i)).comp
      (ModuleCat.castLinearMap (congrArg A.X (by rw [hs i])) LinearMap.id))

/-- The specified relabelling is a DG morphism. -/
def reindex {I J : Type v} (s : I → ℤ) (t : J → ℤ)
    (h : I → J) (hs : ∀ i, s i = t (h i)) :
    freeCells (A := A) s ⟶ freeCells (A := A) t where
  hom := reindexLinear s t h hs
  comm_d := by sorry
  comm_smul := by sorry

/-- A family of cycles gives a DG map by its actual right `A`-linear extension. -/
def fromCycles {I : Type v} (s : I → ℤ)
    (M : DifferentialGradedModule.{u, v} A) (z : ∀ i, M.X (s i))
    (hz : ∀ i, M.d (s i) (z i) = 0) : freeCells (A := A) s ⟶ M where
  hom := evaluation s M z
  comm_d := by sorry
  comm_smul := by sorry

/-- The complete set of homogeneous cycles, rather than chosen representatives. -/
def CycleIndex (M : DifferentialGradedModule.{u, v} A) : Type v :=
  Σ n : ℤ, {z : M.X n // M.d n z = 0}

/-- Stage zero is free on every homogeneous cycle of the target. -/
abbrev initial (M : DifferentialGradedModule.{u, v} A) :
    DifferentialGradedModule.{u, v} A := freeCells (fun i : CycleIndex M ↦ i.1)

/-- Stage-zero augmentation sends the generator indexed by a cycle to that cycle. -/
def initialπ (M : DifferentialGradedModule.{u, v} A) : initial M ⟶ M :=
  fromCycles (fun i : CycleIndex M ↦ i.1) M (fun i ↦ i.2.1) (fun i ↦ i.2.2)

/-- Target maps act on all cycle labels by their stored degreewise functions. -/
def cycleIndexMap {M N : DifferentialGradedModule.{u, v} A} (f : M ⟶ N) :
    CycleIndex M → CycleIndex N := fun i ↦
  ⟨i.1, f.hom i.1 i.2.1, by
    rw [← f.comm_d, i.2.2, map_zero]⟩

/-- The actual functorial stage-zero comparison. -/
def initialMap {M N : DifferentialGradedModule.{u, v} A} (f : M ⟶ N) :
    initial M ⟶ initial N :=
  reindex _ _ (cycleIndexMap f) (fun _ ↦ rfl)

/-- An attachment label specifies the new generator degree, its closed boundary, and its
augmentation image, including the equality that makes the augmentation a chain map. -/
structure AttachIndex {P M : DifferentialGradedModule.{u, v} A} (π : P ⟶ M) where
  degree : ℤ
  cycle : P.X (degree + 1)
  closed : P.d (degree + 1) cycle = 0
  image : M.X degree
  boundary : π.hom (degree + 1) cycle = M.d degree image

/-- Free graded cells to add in the next stage. The coefficient universe is `v`. -/
abbrev newCells {P M : DifferentialGradedModule.{u, v} A} (π : P ⟶ M) :
    DifferentialGradedModule.{u, v} A :=
  freeCells (fun i : AttachIndex π ↦ i.degree)

/-- The off-diagonal differential on one cell coefficient is `c · a`. -/
def boundarySummand {P M : DifferentialGradedModule.{u, v} A} (π : P ⟶ M)
    (n : ℤ) (i : AttachIndex π) : A.X (n + -i.degree) →ₗ[R] P.X (n + 1) :=
  ModuleCat.castLinearMap (congrArg P.X (by omega))
    (P.smul (i.degree + 1) (n + -i.degree) i.cycle)

/-- Extend the off-diagonal differential over the actual direct sum. -/
def boundaryLinear {P M : DifferentialGradedModule.{u, v} A} (π : P ⟶ M) (n : ℤ) :
    (newCells π).X n →ₗ[R] P.X (n + 1) := by
  classical
  exact DirectSum.toModule R (AttachIndex π) _ (boundarySummand π n)

/-- The attached module is the graded direct sum `P ⊕ newCells π`, with
`d(p,x) = (d p + boundary x, d x)`. In particular `d(e_(c,m)) = c`. -/
def attach {P M : DifferentialGradedModule.{u, v} A} (π : P ⟶ M) :
    DifferentialGradedModule.{u, v} A where
  X n := ModuleCat.of R (P.X n × (newCells π).X n)
  d n := ((P.d n).comp (LinearMap.fst R _ _) +
      (boundaryLinear π n).comp (LinearMap.snd R _ _)).prod
    ((newCells π).d n |>.comp (LinearMap.snd R _ _))
  smul p i :=
    { toFun := fun x ↦
        (P.smul p i x.1).prod ((newCells π).smul p i x.2)
      map_add' := by sorry
      map_smul' := by sorry }
  d_sq := by sorry
  smul_one := by sorry
  smul_mul := by sorry
  comm_d := by sorry

/-- Actual stage transition, inclusion into the first coordinate. -/
def inclusion {P M : DifferentialGradedModule.{u, v} A} (π : P ⟶ M) : P ⟶ attach π where
  hom n := LinearMap.inl R _ _
  comm_d := by sorry
  comm_smul := by sorry

/-- The next augmentation sends each new generator `(c,m)` to `m`. -/
def attachπ {P M : DifferentialGradedModule.{u, v} A} (π : P ⟶ M) : attach π ⟶ M where
  hom n := (π.hom n).comp (LinearMap.fst R _ _) +
    (evaluation (fun i : AttachIndex π ↦ i.degree) M (fun i ↦ i.image) n).comp
      (LinearMap.snd R _ _)
  comm_d := by sorry
  comm_smul := by sorry

/-- Projection to the explicit successive free piece is a DG map. -/
def projection {P M : DifferentialGradedModule.{u, v} A} (π : P ⟶ M) :
    attach π ⟶ newCells π where
  hom n := LinearMap.snd R _ _
  comm_d := by sorry
  comm_smul := by sorry

/-- The underlying graded splitting is inclusion into the second coordinate. It is deliberately
not asserted to be a DG map: the new generator has boundary `c`. -/
def gradedSection {P M : DifferentialGradedModule.{u, v} A} (π : P ⟶ M) :
    Graded.Hom (newCells π).toGraded (attach π).toGraded where
  hom n := LinearMap.inr R _ _
  comm_smul := by sorry

/-- A commuting square sends the label `(c,m)` to `(g(c),f(m))`. -/
def attachIndexMap {P Q M N : DifferentialGradedModule.{u, v} A}
    {π : P ⟶ M} {ρ : Q ⟶ N} (g : P ⟶ Q) (f : M ⟶ N)
    (h : g ≫ ρ = π ≫ f) : AttachIndex π → AttachIndex ρ := fun i ↦
  { degree := i.degree
    cycle := g.hom (i.degree + 1) i.cycle
    closed := by rw [← g.comm_d, i.closed, map_zero]
    image := f.hom i.degree i.image
    boundary := by sorry }

/-- The actual attached comparison is block diagonal, with the induced relabelling on new cells. -/
def attachMap {P Q M N : DifferentialGradedModule.{u, v} A}
    {π : P ⟶ M} {ρ : Q ⟶ N} (g : P ⟶ Q) (f : M ⟶ N)
    (h : g ≫ ρ = π ≫ f) : attach π ⟶ attach ρ where
  hom n := (g.hom n).prodMap
    (reindexLinear (fun i : AttachIndex π ↦ i.degree)
      (fun i : AttachIndex ρ ↦ i.degree) (attachIndexMap g f h) (fun _ ↦ rfl) n)
  comm_d := by sorry
  comm_smul := by sorry

@[simp] theorem inclusion_attachπ {P M : DifferentialGradedModule.{u, v} A} (π : P ⟶ M) :
    inclusion π ≫ attachπ π = π := by sorry

@[simp] theorem initialMap_naturality {M N : DifferentialGradedModule.{u, v} A} (f : M ⟶ N) :
    initialMap f ≫ initialπ N = initialπ M ≫ f := by sorry

@[simp] theorem attachMap_naturality {P Q M N : DifferentialGradedModule.{u, v} A}
    {π : P ⟶ M} {ρ : Q ⟶ N} (g : P ⟶ Q) (f : M ⟶ N)
    (h : g ≫ ρ = π ≫ f) : attachMap g f h ≫ attachπ ρ = attachπ π ≫ f := by sorry

/-- The unit coefficient in the generator's degree, with its actual degree transport. -/
def cellUnit {I : Type v} (s : I → ℤ) (i : I) : A.X (s i + -s i) :=
  cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) (add_neg_cancel (s i)).symm) A.one

/-- The actual free generator with coefficient one. -/
def cellGenerator {I : Type v} (s : I → ℤ) (i : I) : (freeCells (A := A) s).X (s i) :=
  cellCoeff s (s i) i (cellUnit s i)

/-- The actual newly attached generator has zero old coordinate and unit new coefficient. -/
def attachedGenerator {P M : DifferentialGradedModule.{u, v} A} (π : P ⟶ M)
    (i : AttachIndex π) : (attach π).X i.degree :=
  (0, cellGenerator (fun i : AttachIndex π ↦ i.degree) i)

/-- Evaluation on a single coefficient is the specified action on the generator image. -/
theorem evaluation_cellCoeff {I : Type v} (s : I → ℤ)
    (M : DifferentialGradedModule.{u, v} A) (z : ∀ i, M.X (s i))
    (n : ℤ) (i : I) (a : A.X (n + -s i)) :
    evaluation s M z n (cellCoeff s n i a) = evaluationSummand s M z n i a := by
  classical
  exact DirectSum.toModule_lof R (M := fun j ↦ (A.X (n + -s j) : Type v))
    (φ := evaluationSummand s M z n) i a

/-- The off-diagonal differential on each coefficient is the actual old-cycle action. -/
theorem boundaryLinear_cellCoeff {P M : DifferentialGradedModule.{u, v} A} (π : P ⟶ M)
    (n : ℤ) (i : AttachIndex π) (a : A.X (n + -i.degree)) :
    boundaryLinear π n (cellCoeff (fun i : AttachIndex π ↦ i.degree) n i a) =
      boundarySummand π n i a := by
  classical
  exact DirectSum.toModule_lof R (M := fun j : AttachIndex π ↦ (A.X (n + -j.degree) : Type v))
    (φ := boundarySummand π n) i a

/-- The differential on a free coefficient is the shifted algebra differential, including
its sign. This statement specializes correctly when `2 = 0`. -/
theorem free_d_cellCoeff {I : Type v} (s : I → ℤ) (n : ℤ) (i : I)
    (a : A.X (n + -s i)) :
    (freeCells (A := A) s).d n (cellCoeff s n i a) =
      cellCoeff s (n + 1) i
        (ModuleCat.castLinearMap
          (congrArg A.X (DifferentialGradedModule.shift_d_index n (-s i)))
          (((-s i).negOnePow : R) • (A.d (n + -s i)).hom) a) := by
  sorry

/-- The new generator has the prescribed cycle as its boundary. -/
theorem d_attachedGenerator {P M : DifferentialGradedModule.{u, v} A} (π : P ⟶ M)
    (i : AttachIndex π) :
    (attach π).d i.degree (attachedGenerator π i) =
      (inclusion π).hom (i.degree + 1) i.cycle := by sorry

/-- The new generator maps to the specified target element. -/
theorem π_attachedGenerator {P M : DifferentialGradedModule.{u, v} A} (π : P ⟶ M)
    (i : AttachIndex π) :
    (attachπ π).hom i.degree (attachedGenerator π i) = i.image := by sorry

/-- Stage zero hits every target cycle on its corresponding actual free generator. -/
theorem initialπ_cellGenerator (M : DifferentialGradedModule.{u, v} A) (i : CycleIndex M) :
    (initialπ M).hom i.1 (cellGenerator (fun j : CycleIndex M ↦ j.1) i) = i.2.1 := by sorry

end DifferentialGradedModule.PropertyP.PrivateConstruction
