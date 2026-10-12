/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Logic.Equiv.Basic
public import ReasLib.RingTheory.RingHom.SquareZero.Functoriality

/-!
# Fibres of square-zero extension classification

The classes of solutions inducing a prescribed map on kernels form the fibre of
restriction on naive cotangent Ext¹ over the coefficient image of the
tautological extension class.
-/

@[expose] public section

noncomputable section

universe u

namespace RingHom.SquareZeroExtension

variable {A' A : Type u} [CommRing A'] [CommRing A]
variable (π : A' →+* A) [π.IsSquareZeroExtension]

/-- The A'-algebra structure on A with structure map π. -/
abbrev algebraOfSquareZero : Algebra A' A :=
  π.toAlgebra

/-- The structure map of the algebra selected by π is π. -/
theorem algebraMap_algebraOfSquareZero :
    -- Local instance justification (noncanonical choice): the explicit π selects the A'-algebra structure among competing ring homomorphisms.
    letI := algebraOfSquareZero π
    algebraMap A' A = π := sorry

/-- Restriction of scalars of an A-module along π. -/
abbrev moduleRestrictScalars (N : Type u) [AddCommGroup N] [Module A N] : Module A' N :=
  Module.compHom N π

/-- The kernel of π is an A'-A scalar tower for the algebra selected by π. -/
instance isScalarTower_kernelModule :
    -- Local instance justification (noncanonical choice): the explicit π selects the A'-algebra structure among competing ring homomorphisms.
    letI := algebraOfSquareZero π
    IsScalarTower A' A (KernelModule π) := sorry

set_option backward.privateInPublic true in
/-- The identity structure map and π commute with the algebra structure selected by π. -/
private theorem selfSolution_commRight :
    -- Local instance justification (noncanonical choice): the explicit π selects the A'-algebra structure among competing ring homomorphisms.
    letI := algebraOfSquareZero π
    π.comp (RingHom.id A') = (structureMap : A' →+* A).comp (RingHom.id A') := sorry

set_option backward.privateInPublic true in
/-- The identity structure map induces the zero map from the kernel of the identity. -/
private theorem selfSolution_induces :
    -- Local instance justification (noncanonical choice): the explicit π selects the A'-algebra structure among competing ring homomorphisms.
    letI := algebraOfSquareZero π
    ∀ x : KernelModule (RingHom.id A'),
      (LinearEquiv.refl A (KernelModule π))
          (kerMapOf (RingHom.id A') (RingHom.id A') π (selfSolution_commRight π) x) =
        zeroKernelMap A' A (KernelModule π) x := sorry

set_option backward.privateInPublic true in
/-- The tautological identity-diagram solution has middle ring A' and projection π. -/
def selfSolution :
    -- Local instance justification (noncanonical choice): the explicit π selects the A'-algebra structure among competing ring homomorphisms.
    letI := algebraOfSquareZero π
    Solution (B := A) (RingHom.id A') (zeroKernelMap A' A (KernelModule π)) :=
  -- Local instance justification (noncanonical choice): the explicit π selects the A'-algebra structure among competing ring homomorphisms.
  letI := algebraOfSquareZero π
  Solution.of (RingHom.id A') (zeroKernelMap A' A (KernelModule π))
    (RingHom.id A') π (selfSolution_commRight π)
    (LinearEquiv.refl A (KernelModule π)) (selfSolution_induces π)

/-- The carrier of the tautological solution is A'. -/
theorem selfSolution_carrier :
    -- Local instance justification (noncanonical choice): the explicit π selects the A'-algebra structure among competing ring homomorphisms.
    letI := algebraOfSquareZero π
    (selfSolution π).carrier = A' := sorry

/-- The structure map of the tautological solution is the identity on A'. -/
theorem selfSolution_fromA' :
    -- Local instance justification (noncanonical choice): the explicit π selects the A'-algebra structure among competing ring homomorphisms.
    letI := algebraOfSquareZero π
    (selfSolution π).fromA' = RingHom.id A' := sorry

/-- The projection of the tautological solution is π. -/
theorem selfSolution_toB :
    -- Local instance justification (noncanonical choice): the explicit π selects the A'-algebra structure among competing ring homomorphisms.
    letI := algebraOfSquareZero π
    (selfSolution π).toB = π := sorry

/-- The naive Ext¹ class ξ of the tautological extension A' of A by ker π. -/
def selfExtensionClass :
    -- Local instance justification (noncanonical choice): the explicit π selects the A'-algebra structure among competing ring homomorphisms.
    letI := algebraOfSquareZero π
    extOneNaiveCotangent A' A (KernelModule π) :=
  -- Local instance justification (noncanonical choice): the explicit π selects the A'-algebra structure among competing ring homomorphisms.
  letI := algebraOfSquareZero π
  (algebraExtensionEquiv A' A (KernelModule π)).symm (isoClassMk (selfSolution π))

/-- The tautological class is the inverse algebra-extension chart of the tautological solution. -/
theorem selfExtensionClass_spec :
    -- Local instance justification (noncanonical choice): the explicit π selects the A'-algebra structure among competing ring homomorphisms.
    letI := algebraOfSquareZero π
    selfExtensionClass π =
      (algebraExtensionEquiv A' A (KernelModule π)).symm (isoClassMk (selfSolution π)) := sorry

variable (B : Type u) [CommRing B] [Algebra A B]

/-- The A'-algebra structure on B with structure map (algebraMap A B).comp π. -/
abbrev algebraCompOfSquareZero : Algebra A' B :=
  ((algebraMap A B).comp π).toAlgebra

/-- The structure map of the composite algebra is the composite of π with A → B. -/
theorem algebraMap_algebraCompOfSquareZero :
    -- Local instance justification (noncanonical choice): π and the A-algebra structure select the composite A'-algebra structure on B.
    letI := algebraCompOfSquareZero π B
    algebraMap A' B = (algebraMap A B).comp π := sorry

/-- The selected maps A' → A → B form an algebra tower. -/
instance isScalarTower_algebra :
    -- Local instance justification (noncanonical choice): the explicit π selects the A'-algebra structure among competing ring homomorphisms.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): π and the A-algebra structure select the composite A'-algebra structure on B.
    letI := algebraCompOfSquareZero π B
    IsScalarTower A' A B := sorry

variable {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
variable (c : KernelModule π →ₗ[A] N)

/-- Scalar multiplication after restriction along π is the A-action of π r. -/
theorem moduleRestrictScalars_smul (r : A') (n : N) :
    -- Local instance justification (noncanonical choice): π selects restriction of the given A-action on N to A'.
    letI : Module A' N := moduleRestrictScalars π N
    r • n = π r • n := sorry

/-- Restriction along π makes N an A'-A scalar tower. -/
instance isScalarTower_moduleA :
    -- Local instance justification (noncanonical choice): the explicit π selects the A'-algebra structure among competing ring homomorphisms.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): π selects restriction of the given A-action on N to A'.
    letI : Module A' N := moduleRestrictScalars π N
    IsScalarTower A' A N := sorry

/-- The restricted A'-action and the B-action on N form a scalar tower. -/
instance isScalarTower_moduleB :
    -- Local instance justification (noncanonical choice): π and the A-algebra structure select the composite A'-algebra structure on B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (noncanonical choice): π selects restriction of the given A-action on N to A'.
    letI : Module A' N := moduleRestrictScalars π N
    IsScalarTower A' B N := sorry

set_option backward.privateInPublic true in
/-- The maps of a solution commute with the composite A'-algebra structure on B. -/
private theorem toIdentitySolution_commRight (S : Solution (B := B) π c) :
    -- Local instance justification (noncanonical choice): π and the A-algebra structure select the composite A'-algebra structure on B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (proof-local temporary data): the stored ring structure on the solution carrier determines the ring homomorphisms.
    letI := S.commRing
    S.toB.comp S.fromA' = (structureMap : A' →+* B).comp (RingHom.id A') := sorry

set_option backward.privateInPublic true in
/-- Forgetting the prescribed coefficient map induces zero on the identity kernel. -/
private theorem toIdentitySolution_induces (S : Solution (B := B) π c) :
    -- Local instance justification (noncanonical choice): π and the A-algebra structure select the composite A'-algebra structure on B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (noncanonical choice): π selects restriction of the given A-action on N to A'.
    letI : Module A' N := moduleRestrictScalars π N
    -- Local instance justification (proof-local temporary data): the stored ring structure on the solution carrier determines the ring homomorphisms.
    letI := S.commRing
    -- Local instance justification (proof-local temporary data): the stored square-zero law determines the kernel module of the solution projection.
    letI := S.isSquareZero
    ∀ x : KernelModule (RingHom.id A'),
      S.kernelEquiv
          (kerMapOf (RingHom.id A') S.fromA' S.toB
            (toIdentitySolution_commRight π B c S) x) =
        zeroKernelMap A' B N x := sorry

set_option backward.privateInPublic true in
/-- Forget the prescribed coefficient map to obtain an A'-algebra extension of B by N. -/
def toIdentitySolution (S : Solution (B := B) π c) :
    -- Local instance justification (noncanonical choice): π and the A-algebra structure select the composite A'-algebra structure on B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (noncanonical choice): π selects restriction of the given A-action on N to A'.
    letI : Module A' N := moduleRestrictScalars π N
    Solution (B := B) (RingHom.id A') (zeroKernelMap A' B N) :=
  -- Local instance justification (noncanonical choice): π and the A-algebra structure select the composite A'-algebra structure on B.
  letI := algebraCompOfSquareZero π B
  -- Local instance justification (noncanonical choice): π selects restriction of the given A-action on N to A'.
  letI : Module A' N := moduleRestrictScalars π N
  -- Local instance justification (proof-local temporary data): the stored ring structure on the solution carrier determines the ring homomorphisms.
  letI := S.commRing
  -- Local instance justification (proof-local temporary data): the stored square-zero law determines the kernel module of the solution projection.
  letI := S.isSquareZero
  Solution.of (RingHom.id A') (zeroKernelMap A' B N) S.fromA' S.toB
    (toIdentitySolution_commRight π B c S) S.kernelEquiv
    (toIdentitySolution_induces π B c S)

/-- Forgetting to the identity diagram preserves the structure map from A'. -/
theorem toIdentitySolution_fromA' (S : Solution (B := B) π c) :
    -- Local instance justification (noncanonical choice): π and the A-algebra structure select the composite A'-algebra structure on B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (noncanonical choice): π selects restriction of the given A-action on N to A'.
    letI : Module A' N := moduleRestrictScalars π N
    (toIdentitySolution π B c S).fromA' = S.fromA' := sorry

set_option backward.privateInPublic true in
/-- Isomorphic solutions have the same underlying A'-algebra extension class. -/
private theorem toExtClass_respectsIso :
    -- Local instance justification (noncanonical choice): π and the A-algebra structure select the composite A'-algebra structure on B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (noncanonical choice): π selects restriction of the given A-action on N to A'.
    letI : Module A' N := moduleRestrictScalars π N
    ∀ (first second : Solution (B := B) π c), (isoSetoid π B c).r first second →
      (algebraExtensionEquiv A' B N).symm (isoClassMk (toIdentitySolution π B c first)) =
        (algebraExtensionEquiv A' B N).symm (isoClassMk (toIdentitySolution π B c second)) := sorry

set_option backward.privateInPublic true in
/-- The naive Ext¹ class attached to an isomorphism class of solutions. -/
def toExtClass (p : IsoClass π B c) :
    -- Local instance justification (noncanonical choice): π and the A-algebra structure select the composite A'-algebra structure on B.
    letI := algebraCompOfSquareZero π B
    extOneNaiveCotangent A' B N :=
  -- Local instance justification (noncanonical choice): π and the A-algebra structure select the composite A'-algebra structure on B.
  letI := algebraCompOfSquareZero π B
  -- Local instance justification (noncanonical choice): π selects restriction of the given A-action on N to A'.
  letI : Module A' N := moduleRestrictScalars π N
  Quotient.liftOn p
    (fun S ↦ (algebraExtensionEquiv A' B N).symm (isoClassMk (toIdentitySolution π B c S)))
    (toExtClass_respectsIso π B c)

/-- On a representative the class map is the inverse algebra-extension chart. -/
theorem toExtClass_mk (S : Solution (B := B) π c) :
    -- Local instance justification (noncanonical choice): π and the A-algebra structure select the composite A'-algebra structure on B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (noncanonical choice): π selects restriction of the given A-action on N to A'.
    letI : Module A' N := moduleRestrictScalars π N
    toExtClass π B c (isoClassMk S) =
      (algebraExtensionEquiv A' B N).symm (isoClassMk (toIdentitySolution π B c S)) := sorry

/-- The fibre of restriction on Ext¹ over the coefficient image of the tautological class. -/
abbrev solutionExtFiber :=
  -- Local instance justification (noncanonical choice): the explicit π selects the A'-algebra structure among competing ring homomorphisms.
  letI := algebraOfSquareZero π
  -- Local instance justification (noncanonical choice): π and the A-algebra structure select the composite A'-algebra structure on B.
  letI := algebraCompOfSquareZero π B
  {ζ : extOneNaiveCotangent A' B N //
    extOneNaiveCotangent_comap A ζ = extOneNaiveCotangent_map c (selfExtensionClass π)}

/-- A fibre element restricts to the coefficient image of the tautological class. -/
theorem mem_solutionExtFiber (ζ : solutionExtFiber π B c) :
    -- Local instance justification (noncanonical choice): the explicit π selects the A'-algebra structure among competing ring homomorphisms.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): π and the A-algebra structure select the composite A'-algebra structure on B.
    letI := algebraCompOfSquareZero π B
    extOneNaiveCotangent_comap A ζ.val =
      extOneNaiveCotangent_map c (selfExtensionClass π) := sorry

/-- The class of every solution belongs to the fibre over the prescribed coefficient image. -/
theorem toExtClass_mem (p : IsoClass π B c) :
    -- Local instance justification (noncanonical choice): the explicit π selects the A'-algebra structure among competing ring homomorphisms.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): π and the A-algebra structure select the composite A'-algebra structure on B.
    letI := algebraCompOfSquareZero π B
    extOneNaiveCotangent_comap A (toExtClass π B c p) =
      extOneNaiveCotangent_map c (selfExtensionClass π) := sorry

set_option backward.privateInPublic true in
/-- An identity-diagram extension commutes with the original square-zero projection. -/
private theorem ofFiber_commRight :
    -- Local instance justification (noncanonical choice): π and the A-algebra structure select the composite A'-algebra structure on B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (noncanonical choice): π selects restriction of the given A-action on N to A'.
    letI : Module A' N := moduleRestrictScalars π N
    ∀ SB : Solution (B := B) (RingHom.id A') (zeroKernelMap A' B N),
      -- Local instance justification (proof-local temporary data): the stored ring structure on the extension carrier determines the ring homomorphisms.
      letI := SB.commRing
      SB.toB.comp SB.fromA' = (structureMap : A →+* B).comp π := sorry

set_option backward.privateInPublic true in
/-- An extension whose restricted class equals the prescribed coefficient image induces c. -/
private theorem ofFiber_induces :
    -- Local instance justification (noncanonical choice): the explicit π selects the A'-algebra structure among competing ring homomorphisms.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): π and the A-algebra structure select the composite A'-algebra structure on B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (noncanonical choice): π selects restriction of the given A-action on N to A'.
    letI : Module A' N := moduleRestrictScalars π N
    ∀ (SB : Solution (B := B) (RingHom.id A') (zeroKernelMap A' B N)),
      extOneNaiveCotangent_comap A ((algebraExtensionEquiv A' B N).symm (isoClassMk SB)) =
        extOneNaiveCotangent_map c (selfExtensionClass π) →
      -- Local instance justification (proof-local temporary data): the stored ring structure on the extension carrier determines the ring homomorphisms.
      letI := SB.commRing
      -- Local instance justification (proof-local temporary data): the stored square-zero law determines the kernel module of the extension projection.
      letI := SB.isSquareZero
      ∀ x : KernelModule π,
        SB.kernelEquiv (kerMapOf π SB.fromA' SB.toB (ofFiber_commRight π B SB) x) =
          c x := sorry

set_option backward.privateInPublic true in
/-- Reinterpret a compatible identity-diagram extension as a solution inducing c. -/
private def ofFiberRepresentative :
    -- Local instance justification (noncanonical choice): the explicit π selects the A'-algebra structure among competing ring homomorphisms.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): π and the A-algebra structure select the composite A'-algebra structure on B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (noncanonical choice): π selects restriction of the given A-action on N to A'.
    letI : Module A' N := moduleRestrictScalars π N
    (SB : Solution (B := B) (RingHom.id A') (zeroKernelMap A' B N)) →
      (extOneNaiveCotangent_comap A ((algebraExtensionEquiv A' B N).symm (isoClassMk SB)) =
        extOneNaiveCotangent_map c (selfExtensionClass π)) → IsoClass π B c :=
  -- Local instance justification (noncanonical choice): the explicit π selects the A'-algebra structure among competing ring homomorphisms.
  letI := algebraOfSquareZero π
  -- Local instance justification (noncanonical choice): π and the A-algebra structure select the composite A'-algebra structure on B.
  letI := algebraCompOfSquareZero π B
  -- Local instance justification (noncanonical choice): π selects restriction of the given A-action on N to A'.
  letI : Module A' N := moduleRestrictScalars π N
  fun SB hCompatibility ↦
    -- Local instance justification (proof-local temporary data): the stored ring structure on the extension carrier determines the ring homomorphisms.
    letI := SB.commRing
    -- Local instance justification (proof-local temporary data): the stored square-zero law determines the kernel module of the extension projection.
    letI := SB.isSquareZero
    isoClassMk (Solution.of π c SB.fromA' SB.toB (ofFiber_commRight π B SB)
      SB.kernelEquiv (ofFiber_induces π B c SB hCompatibility))

set_option backward.privateInPublic true in
/-- Reconstruction as a function of compatibility evidence is invariant under extension isomorphism. -/
private theorem ofFiberRepresentative_congr :
    -- Local instance justification (noncanonical choice): the explicit π selects the A'-algebra structure among competing ring homomorphisms.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): π and the A-algebra structure select the composite A'-algebra structure on B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (noncanonical choice): π selects restriction of the given A-action on N to A'.
    letI : Module A' N := moduleRestrictScalars π N
    ∀ (first second : Solution (B := B) (RingHom.id A') (zeroKernelMap A' B N)),
      (isoSetoid (RingHom.id A') B (zeroKernelMap A' B N)).r first second →
        HEq (ofFiberRepresentative π B c first) (ofFiberRepresentative π B c second) := sorry

set_option backward.privateInPublic true in
/-- Classifying a fibre element as an algebra extension preserves its restriction equality. -/
private theorem ofFiber_class_mem (ζ : solutionExtFiber π B c) :
    -- Local instance justification (noncanonical choice): the explicit π selects the A'-algebra structure among competing ring homomorphisms.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): π and the A-algebra structure select the composite A'-algebra structure on B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (noncanonical choice): π selects restriction of the given A-action on N to A'.
    letI : Module A' N := moduleRestrictScalars π N
    extOneNaiveCotangent_comap A
        ((algebraExtensionEquiv A' B N).symm (algebraExtensionEquiv A' B N ζ.val)) =
      extOneNaiveCotangent_map c (selfExtensionClass π) := sorry

set_option backward.privateInPublic true in
/-- Reconstruct an isomorphism class of solutions from an element of the Ext¹ fibre. -/
def ofFiber (ζ : solutionExtFiber π B c) : IsoClass π B c :=
  -- Local instance justification (noncanonical choice): the explicit π selects the A'-algebra structure among competing ring homomorphisms.
  letI := algebraOfSquareZero π
  -- Local instance justification (noncanonical choice): π and the A-algebra structure select the composite A'-algebra structure on B.
  letI := algebraCompOfSquareZero π B
  -- Local instance justification (noncanonical choice): π selects restriction of the given A-action on N to A'.
  letI : Module A' N := moduleRestrictScalars π N
  let P := fun q : IsoClass (RingHom.id A') B (zeroKernelMap A' B N) ↦
    extOneNaiveCotangent_comap A ((algebraExtensionEquiv A' B N).symm q) =
      extOneNaiveCotangent_map c (selfExtensionClass π)
  (Quotient.hrecOn (motive := fun q ↦ P q → IsoClass π B c)
    (algebraExtensionEquiv A' B N ζ.val)
    (fun SB hCompatibility ↦ ofFiberRepresentative π B c SB hCompatibility)
    (ofFiberRepresentative_congr π B c)) (ofFiber_class_mem π B c ζ)

/-- The Ext¹ class of a reconstructed solution recovers the fibre element. -/
theorem toExtClass_ofFiber (ζ : solutionExtFiber π B c) :
    toExtClass π B c (ofFiber π B c ζ) = ζ.val := sorry

/-- Reconstructing the class of a solution recovers its isomorphism class. -/
theorem ofFiber_toExtClass (p : IsoClass π B c) :
    ofFiber π B c ⟨toExtClass π B c p, toExtClass_mem π B c p⟩ = p := sorry

/-- Solution classes are canonically equivalent to the fibre of restriction over the tautological class. -/
def isoClassFiberEquiv : IsoClass π B c ≃ solutionExtFiber π B c where
  toFun p := ⟨toExtClass π B c p, toExtClass_mem π B c p⟩
  invFun := ofFiber π B c
  left_inv := ofFiber_toExtClass π B c
  right_inv ζ := Subtype.ext (toExtClass_ofFiber π B c ζ)

/-- The fibre equivalence sends a solution class to its naive Ext¹ class. -/
theorem isoClassFiberEquiv_apply (p : IsoClass π B c) :
    (isoClassFiberEquiv π B c p).val = toExtClass π B c p := sorry

/-- The inverse fibre equivalence reconstructs a solution class. -/
theorem isoClassFiberEquiv_symm_apply (ζ : solutionExtFiber π B c) :
    (isoClassFiberEquiv π B c).symm ζ = ofFiber π B c ζ := sorry

/-- Solutions exist exactly when the coefficient image of the tautological class lies in the restriction image. -/
theorem isoClassFiberEquiv_nonempty_iff :
    Nonempty (IsoClass π B c) ↔ Nonempty (solutionExtFiber π B c) := sorry

end RingHom.SquareZeroExtension
