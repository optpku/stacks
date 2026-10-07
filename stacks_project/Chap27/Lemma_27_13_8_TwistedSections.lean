module

public import ReasLib.Algebra.DirectSum.NatToInt
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.TensorUnit
public import ReasLib.Algebra.Module.Graded.Left
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.GlobalSections
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Presentation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import stacks_project.Chap27.Lemma_27_8_7_AssociatedSheaf
public import stacks_project.Chap27.Lemma_27_10_2

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The degree-`d` global sections of a quasi-coherent module tensored with the chosen twist
`𝒪(d)` on projective space. -/
abbrev twistedSection (P : ProjTwistPresentation (grading R n))
    (F : Scheme.QCoh (scheme R n)) (d : ℕ) : Type u :=
  Γ(P.tensorTwist ((Scheme.QCoh.inclusion (scheme R n)).obj F) d, ⊤)

/-- The nonnegative direct sum of the twisted global sections of `F`. -/
abbrev twistedSections (P : ProjTwistPresentation (grading R n))
    (F : Scheme.QCoh (scheme R n)) : Type u :=
  ⨁ d : ℕ, twistedSection P F d

/-- The degree-`d` homogeneous polynomials in `R[T₀, …, Tₙ]`. -/
abbrev polynomialPiece (R : Type u) [CommRing R] (n d : ℕ) : Type u :=
  grading R n d

/-- `polynomialPiece R n d` is the degree-`d` part of the standard polynomial grading. -/
theorem polynomialPiece_def (R : Type u) [CommRing R] (n d : ℕ) :
    polynomialPiece R n d = grading R n d := sorry

namespace TwistedSections

/-- Reindex a twisted section along equality of its integral twist degrees. -/
noncomputable def reindex (P : ProjTwistPresentation (grading R n))
    (F : Scheme.QCoh (scheme R n)) {a b : ℤ} (h : a = b) :
    Γ(P.tensorTwist ((Scheme.QCoh.inclusion (scheme R n)).obj F) a, ⊤) →+
      Γ(P.tensorTwist ((Scheme.QCoh.inclusion (scheme R n)).obj F) b, ⊤) :=
  AddEquiv.toAddMonoidHom (AddEquiv.cast (congrArg (fun d ↦
    Γ(P.tensorTwist ((Scheme.QCoh.inclusion (scheme R n)).obj F) d, ⊤)) h))

/-- The additive action of one fixed homogeneous polynomial on one twisted-section degree. -/
noncomputable def actionHom (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) (e d : ℕ) (a : grading R n e) :
    twistedSection P F d →+ twistedSection P F (e + d) :=
  (reindex P F (Int.natCast_add e d).symm).comp
    (ProjTwistGlobalSections.homogeneousAction (grading R n) P.actualTwist T.hom
      ((Scheme.QCoh.inclusion (scheme R n)).obj F) e (d : ℤ)
        ((P.actualSectionMap e).hom a))

/-- The fixed-degree action sends the zero homogeneous polynomial to the zero homomorphism. -/
theorem actionHom_zero (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) (e d : ℕ) :
    actionHom P T F e d (0 : grading R n e) = 0 := sorry

/-- The fixed-degree action sends a sum of homogeneous polynomials to the sum of homomorphisms. -/
theorem actionHom_add (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) (e d : ℕ)
    (a b : grading R n e) :
    actionHom P T F e d (a + b) = actionHom P T F e d a + actionHom P T F e d b := sorry

/-- A degree-`e` homogeneous polynomial acts on a degree-`d` twisted section through the
chosen multiplication maps for the actual twists. -/
noncomputable def action (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) (e d : ℕ) :
    grading R n e →+ twistedSection P F d →+ twistedSection P F (e + d) where
  toFun := actionHom P T F e d
  map_zero' := actionHom_zero P T F e d
  map_add' := actionHom_add P T F e d

/-- The action formula is the homogeneous twist action followed by the canonical reindexing
from `(e : ℤ) + d` to `e + d`. -/
theorem action_apply (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) (e d : ℕ)
    (a : grading R n e) (s : twistedSection P F d) :
    action P T F e d a s =
      reindex P F (Int.natCast_add e d).symm
        (ProjTwistGlobalSections.homogeneousAction (grading R n) P.actualTwist T.hom
          ((Scheme.QCoh.inclusion (scheme R n)).obj F) e (d : ℤ)
          ((P.actualSectionMap e).hom a) s) := sorry

/-- The explicit homogeneous action as mathlib's external graded scalar operation. -/
@[implicit_reducible]
noncomputable def actionGSMul (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) :
    GradedMonoid.GSMul (polynomialPiece R n) (twistedSection P F) where
  smul := fun {e d} a s ↦ action P T F e d a s

/-- The degree-zero homogeneous unit acts trivially on twisted sections. -/
theorem action_one_smul (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) :
    -- Local instance justification (noncanonical choice): the homogeneous scalar action depends
    -- on the explicit presentations `P` and `T`, so registering it would create diamonds.
    let _ := actionGSMul P T F
    ∀ s : GradedMonoid (twistedSection P F),
      (1 : GradedMonoid (polynomialPiece R n)) • s = s := sorry

/-- Successive homogeneous actions agree with multiplication of homogeneous polynomials. -/
theorem action_mul_smul (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) :
    -- Local instance justification (noncanonical choice): the homogeneous scalar action depends
    -- on the explicit presentations `P` and `T`, so registering it would create diamonds.
    let _ := actionGSMul P T F
    ∀ a b : GradedMonoid (polynomialPiece R n),
      ∀ s : GradedMonoid (twistedSection P F), (a * b) • s = a • b • s := sorry

/-- The homogeneous action is additive in the twisted-section variable. -/
theorem action_smul_add (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) {e d : ℕ}
    (a : grading R n e) (s t : twistedSection P F d) :
    action P T F e d a (s + t) = action P T F e d a s + action P T F e d a t := sorry

/-- Every homogeneous polynomial acts additively on zero. -/
theorem action_smul_zero (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) {e d : ℕ} (a : grading R n e) :
    action P T F e d a (0 : twistedSection P F d) = 0 := sorry

/-- The homogeneous action is additive in the polynomial variable. -/
theorem action_add_smul (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) {e d : ℕ}
    (a b : grading R n e) (s : twistedSection P F d) :
    action P T F e d (a + b) s = action P T F e d a s + action P T F e d b s := sorry

/-- The zero homogeneous polynomial acts as zero. -/
theorem action_zero_smul (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) {e d : ℕ} (s : twistedSection P F d) :
    action P T F e d (0 : grading R n e) s = 0 := sorry

/-- The homogeneous action satisfies the unit and associativity laws. -/
@[implicit_reducible]
noncomputable def actionGMulAction (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) :
    GradedMonoid.GMulAction (polynomialPiece R n) (twistedSection P F) :=
  GradedMonoid.GMulAction.mk (toGSMul := actionGSMul P T F) sorry sorry

/-- The homogeneous action distributes over addition in each twisted-section degree. -/
@[implicit_reducible]
noncomputable def actionGdistribMulAction
    (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) :
    DirectSum.GdistribMulAction (polynomialPiece R n) (twistedSection P F) :=
  DirectSum.GdistribMulAction.mk
    (toGMulAction := actionGMulAction P T F) sorry sorry

/-- The chosen homogeneous action makes the degree pieces an external graded module over the
standard polynomial grading. -/
@[implicit_reducible]
noncomputable def gmodule (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) :
    DirectSum.Gmodule (polynomialPiece R n) (twistedSection P F) :=
  DirectSum.Gmodule.mk
    (toGdistribMulAction := actionGdistribMulAction P T F) sorry sorry

/-- The `R[T₀, …, Tₙ]`-module structure on the nonnegative twisted-section sum. -/
@[implicit_reducible]
noncomputable def moduleStructure (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) :
    Module (MvPolynomial (Fin (n + 1)) R) (twistedSections P F) :=
  -- Local instance justification (noncanonical choice): the graded action depends on the
  -- explicit presentations `P` and `T`, so it cannot be registered on the shared carrier.
  let _ := gmodule P T F
  Module.compHom (twistedSections P F)
    (DirectSum.decomposeRingEquiv (grading R n)).toRingHom

/-- Polynomial scalar multiplication is induced by decomposing the polynomial into homogeneous
pieces and applying the external graded-module action. -/
theorem moduleStructure_smul (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) (a : MvPolynomial (Fin (n + 1)) R)
    (m : twistedSections P F) :
    (moduleStructure P T F).smul a m =
      -- Local instance justification (noncanonical choice): the graded action depends on the
      -- explicit presentations `P` and `T`, so it cannot be registered on the shared carrier.
      let _ := gmodule P T F
      DirectSum.decompose (grading R n) a • m := sorry

/-- Restriction along constant polynomials gives the base-`R` module structure. -/
@[implicit_reducible]
noncomputable def baseModuleStructure (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) : Module R (twistedSections P F) :=
  -- Local instance justification (noncanonical choice): the polynomial module structure depends
  -- on `P` and `T`, so globally registering it would conflate competing presentations.
  let _ := moduleStructure P T F
  Module.compHom (twistedSections P F) (algebraMap R (MvPolynomial (Fin (n + 1)) R))

/-- The base and polynomial actions on twisted sections form the canonical scalar tower. -/
theorem moduleStructure_isScalarTower (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) :
    -- Local instance justification (noncanonical choice): both module structures depend on the
    -- explicit presentations `P` and `T` and are installed only to state their compatibility.
    let _ := baseModuleStructure P T F
    -- Local instance justification (noncanonical choice): the polynomial action depends on the
    -- explicit presentations `P` and `T`, so it cannot be a global instance on this carrier.
    let _ := moduleStructure P T F
    IsScalarTower R (MvPolynomial (Fin (n + 1)) R) (twistedSections P F) := sorry

/-- The carrier set of the degree-`d` summand inside the direct sum of twisted sections. -/
def naturalComponentSet (P : ProjTwistPresentation (grading R n))
    (F : Scheme.QCoh (scheme R n)) (d : ℕ) : Set (twistedSections P F) :=
  Set.range (DirectSum.of (twistedSection P F) d)

/-- Zero belongs to every natural homogeneous component. -/
theorem zero_mem_naturalComponentSet (P : ProjTwistPresentation (grading R n))
    (F : Scheme.QCoh (scheme R n)) (d : ℕ) :
    0 ∈ naturalComponentSet P F d := sorry

/-- Every natural homogeneous component is closed under addition. -/
theorem add_mem_naturalComponentSet (P : ProjTwistPresentation (grading R n))
    (F : Scheme.QCoh (scheme R n)) (d : ℕ) {x y : twistedSections P F}
    (hx : x ∈ naturalComponentSet P F d) (hy : y ∈ naturalComponentSet P F d) :
    x + y ∈ naturalComponentSet P F d := sorry

/-- Every natural homogeneous component is closed under the base-ring action. -/
theorem smul_mem_naturalComponentSet (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) (d : ℕ) :
    -- Local instance justification (noncanonical choice): the base action is induced from the
    -- presentation-dependent polynomial action and is confined to this statement.
    let _ := baseModuleStructure P T F
    ∀ (r : R) {x : twistedSections P F}, x ∈ naturalComponentSet P F d →
      r • x ∈ naturalComponentSet P F d := sorry

/-- The natural grading of the twisted-section direct sum by its summand carriers. -/
noncomputable def naturalGrading (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) :
    -- Local instance justification (noncanonical choice): the base action depends on `P` and `T`
    -- and is installed only to form the corresponding submodules.
    let _ := baseModuleStructure P T F
    ℕ → Submodule R (twistedSections P F) :=
  -- Local instance justification (noncanonical choice): the base action depends on `P` and `T`
  -- and is installed only while constructing the corresponding submodules.
  let _ := baseModuleStructure P T F
  fun d ↦
    { carrier := naturalComponentSet P F d
      zero_mem' := zero_mem_naturalComponentSet P F d
      add_mem' := add_mem_naturalComponentSet P F d
      smul_mem' := smul_mem_naturalComponentSet P T F d }

/-- The carrier of the natural degree-`d` submodule is the range of the direct-sum inclusion. -/
theorem naturalGrading_carrier (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) (d : ℕ) :
    -- Local instance justification (noncanonical choice): the submodule grading uses the
    -- presentation-dependent base action and cannot be registered independently of `P` and `T`.
    let _ := baseModuleStructure P T F
    (naturalGrading P T F d : Set (twistedSections P F)) = naturalComponentSet P F d := sorry

/-- The natural homogeneous pieces form the direct-sum decomposition of twisted sections. -/
theorem naturalGrading_isInternal (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) :
    -- Local instance justification (noncanonical choice): the submodule grading uses the
    -- presentation-dependent base action and cannot be registered independently of `P` and `T`.
    let _ := baseModuleStructure P T F
    DirectSum.IsInternal (naturalGrading P T F) := sorry

/-- A pure degree-`d` twisted section belongs to the degree-`d` natural component. -/
theorem of_mem_naturalGrading (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) (d : ℕ) (x : twistedSection P F d) :
    -- Local instance justification (noncanonical choice): the submodule grading uses the
    -- presentation-dependent base action and cannot be registered independently of `P` and `T`.
    let _ := baseModuleStructure P T F
    DirectSum.of (twistedSection P F) d x ∈ naturalGrading P T F d := sorry

/-- A section in degree `d`, regarded as an element of the corresponding homogeneous
submodule of the full twisted-section direct sum. -/
noncomputable def naturalComponentValue (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) (d : ℕ)
    (x : twistedSection P F d) :
    -- Local instance justification (noncanonical choice): the component subtype is formed using
    -- the base action selected by the explicit presentations `P` and `T`.
    let _ := baseModuleStructure P T F
    naturalGrading P T F d :=
  -- Local instance justification (noncanonical choice): the component subtype is formed using
  -- the base action selected by the explicit presentations `P` and `T`.
  let _ := baseModuleStructure P T F
  ⟨DirectSum.of (twistedSection P F) d x, of_mem_naturalGrading P T F d x⟩

/-- The homogeneous-component inclusion sends zero to zero. -/
theorem naturalComponentValue_zero (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) (d : ℕ) :
    -- Local instance justification (noncanonical choice): the component subtype is formed using
    -- the base action selected by the explicit presentations `P` and `T`.
    let _ := baseModuleStructure P T F
    naturalComponentValue P T F d 0 = 0 := sorry

/-- The homogeneous-component inclusion preserves addition. -/
theorem naturalComponentValue_add (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) (d : ℕ)
    (x y : twistedSection P F d) :
    -- Local instance justification (noncanonical choice): the component subtype is formed using
    -- the base action selected by the explicit presentations `P` and `T`.
    let _ := baseModuleStructure P T F
    naturalComponentValue P T F d (x + y) =
      naturalComponentValue P T F d x + naturalComponentValue P T F d y := sorry

/-- The additive inclusion of one twisted-section summand into its homogeneous submodule. -/
noncomputable def naturalComponentHom (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) (d : ℕ) :
    -- Local instance justification (noncanonical choice): the component subtype is formed using
    -- the base action selected by the explicit presentations `P` and `T`.
    let _ := baseModuleStructure P T F
    twistedSection P F d →+ naturalGrading P T F d :=
  -- Local instance justification (noncanonical choice): the component subtype is formed using
  -- the base action selected by the explicit presentations `P` and `T`.
  let _ := baseModuleStructure P T F
  { toFun := naturalComponentValue P T F d
    map_zero' := naturalComponentValue_zero P T F d
    map_add' := naturalComponentValue_add P T F d }

/-- The explicit decomposition map sending a direct-sum element to the same finite family,
with each entry placed in its homogeneous submodule. -/
noncomputable def naturalDecompose (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) :
    -- Local instance justification (noncanonical choice): the target submodules use the base
    -- action selected by the explicit presentations `P` and `T`.
    let _ := baseModuleStructure P T F
    twistedSections P F →+ ⨁ d : ℕ, naturalGrading P T F d :=
  -- Local instance justification (noncanonical choice): the target submodules use the base
  -- action selected by the explicit presentations `P` and `T`.
  let _ := baseModuleStructure P T F
  DirectSum.toAddMonoid fun d ↦
    (DirectSum.of (fun e ↦ naturalGrading P T F e) d).comp
      (naturalComponentHom P T F d)

/-- Recomposing after `naturalDecompose` is the identity on twisted sections. -/
theorem naturalDecompose_left_inv (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) :
    -- Local instance justification (noncanonical choice): the decomposition uses the base action
    -- selected by the explicit presentations `P` and `T`.
    let _ := baseModuleStructure P T F
    Function.LeftInverse (DirectSum.coeAddMonoidHom (naturalGrading P T F))
      (naturalDecompose P T F) := sorry

/-- Decomposing after recomposition is the identity on the homogeneous-component sum. -/
theorem naturalDecompose_right_inv (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) :
    -- Local instance justification (noncanonical choice): the decomposition uses the base action
    -- selected by the explicit presentations `P` and `T`.
    let _ := baseModuleStructure P T F
    Function.RightInverse (DirectSum.coeAddMonoidHom (naturalGrading P T F))
      (naturalDecompose P T F) := sorry

/-- The natural homogeneous pieces carry their canonical direct-sum decomposition. -/
@[implicit_reducible]
noncomputable def naturalGradingDecomposition
    (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) :
    -- Local instance justification (noncanonical choice): the decomposition uses the base action
    -- selected by the explicit presentations `P` and `T`.
    let _ := baseModuleStructure P T F
    DirectSum.Decomposition (naturalGrading P T F) :=
  -- Local instance justification (noncanonical choice): the decomposition uses the base action
  -- selected by the explicit presentations `P` and `T`.
  let _ := baseModuleStructure P T F
  { decompose' := naturalDecompose P T F
    left_inv := naturalDecompose_left_inv P T F
    right_inv := naturalDecompose_right_inv P T F }

/-- Homogeneous polynomial multiplication respects the natural direct-sum grading. -/
theorem naturalGrading_gradedSMul (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) :
    -- Local instance justification (noncanonical choice): the grading and scalar action depend on
    -- the explicit presentations `P` and `T`, so neither can be registered on the shared carrier.
    let _ := baseModuleStructure P T F
    -- Local instance justification (noncanonical choice): the polynomial action depends on the
    -- explicit presentations `P` and `T`, so it cannot be globally registered here.
    let _ := moduleStructure P T F
    SetLike.GradedSMul (grading R n) (naturalGrading P T F) := sorry

/-- The internal integer grading obtained from the natural grading by setting negative pieces
equal to zero. -/
noncomputable def internalGrading (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) :
    -- Local instance justification (noncanonical choice): the integer grading extends submodules
    -- formed with the base action selected by `P` and `T`.
    let _ := baseModuleStructure P T F
    ℤ → Submodule R (twistedSections P F) :=
  -- Local instance justification (noncanonical choice): the integer grading extends submodules
  -- formed with the base action selected by `P` and `T`.
  let _ := baseModuleStructure P T F
  fun d ↦ if 0 ≤ d then naturalGrading P T F d.toNat else ⊥

/-- In natural degree `d`, the integer grading is the corresponding natural component. -/
theorem internalGrading_nat (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) (d : ℕ) :
    -- Local instance justification (noncanonical choice): the integer grading extends submodules
    -- formed with the base action selected by `P` and `T`.
    let _ := baseModuleStructure P T F
    internalGrading P T F d = naturalGrading P T F d := sorry

/-- Every negative component of the integer grading is zero. -/
theorem internalGrading_neg (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) {d : ℤ} (hd : d < 0) :
    -- Local instance justification (noncanonical choice): the integer grading extends submodules
    -- formed with the base action selected by `P` and `T`.
    let _ := baseModuleStructure P T F
    internalGrading P T F d = ⊥ := sorry

/-- Homogeneous polynomial multiplication respects the integer-extended grading. -/
theorem internalGrading_gradedSMul (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) :
    -- Local instance justification (noncanonical choice): the integer grading and scalar action
    -- depend on the explicit presentations `P` and `T`.
    let _ := baseModuleStructure P T F
    -- Local instance justification (noncanonical choice): the polynomial action depends on the
    -- explicit presentations `P` and `T`, so it cannot be globally registered here.
    let _ := moduleStructure P T F
    SetLike.GradedSMul (grading R n) (internalGrading P T F) := sorry

/-- The nonnegative twisted-section sum as a left graded module over `R[T₀, …, Tₙ]`. -/
noncomputable def gradedModule (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) : GradedModule.Left (grading R n) where
  carrier := twistedSections P F
  addCommMonoid := inferInstance
  moduleBase := baseModuleStructure P T F
  moduleAlgebra := moduleStructure P T F
  isScalarTower := moduleStructure_isScalarTower P T F
  grading := naturalGrading P T F
  decomposition := naturalGradingDecomposition P T F
  gradedSMul := naturalGrading_gradedSMul P T F

/-- The carrier of `gradedModule` is the direct sum of nonnegative twisted sections. -/
theorem gradedModule_carrier (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) :
    (gradedModule P T F : Type u) = twistedSections P F := sorry

/-- The grading of `gradedModule` is its natural direct-sum grading. -/
theorem gradedModule_grading (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) :
    (gradedModule P T F).grading = naturalGrading P T F := sorry

/-- The sheaf on projective space associated to the explicitly graded polynomial module of
nonnegative twisted sections. -/
noncomputable def associatedSheaf (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) : (scheme R n).Modules :=
  -- Local instance justification (noncanonical choice): the base action on the shared direct-sum
  -- carrier depends on the explicit presentations `P` and `T`.
  let _ := baseModuleStructure P T F
  -- Local instance justification (noncanonical choice): the polynomial action on the shared
  -- direct-sum carrier depends on the explicit presentations `P` and `T`.
  let _ := moduleStructure P T F
  -- Local instance justification (noncanonical choice): the graded-scalar law belongs to the
  -- presentation-dependent grading installed only for this associated-sheaf construction.
  let _ := internalGrading_gradedSMul P T F
  Proj.associatedSheaf (grading R n) (internalGrading P T F)

/-- `associatedSheaf` is the canonical Proj sheaf of the bundled twisted-section grading. -/
theorem associatedSheaf_def (P : ProjTwistPresentation (grading R n))
    (T : ProjTwistMulPresentation (grading R n) P)
    (F : Scheme.QCoh (scheme R n)) :
    -- Local instance justification (noncanonical choice): the base action on the shared direct-sum
    -- carrier depends on the explicit presentations `P` and `T`.
    let _ := baseModuleStructure P T F
    -- Local instance justification (noncanonical choice): the polynomial action on the shared
    -- direct-sum carrier depends on the explicit presentations `P` and `T`.
    let _ := moduleStructure P T F
    -- Local instance justification (noncanonical choice): the graded-scalar law belongs to the
    -- presentation-dependent grading installed only for this associated-sheaf formula.
    let _ := internalGrading_gradedSMul P T F
    associatedSheaf P T F =
      Proj.associatedSheaf (grading R n) (internalGrading P T F) := sorry

end TwistedSections

end AlgebraicGeometry.ProjectiveSpace
