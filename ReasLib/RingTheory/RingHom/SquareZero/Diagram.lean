/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.RingHom
public import Mathlib.RingTheory.Derivation.ToSquareZero
public import Mathlib.RingTheory.Kaehler.Basic
public import ReasLib.RingTheory.RingHom.SquareZero.Solution

/-!
# Connecting diagrams of relative square-zero solutions

A relative diagram packages two solutions of relative square-zero solutions together with connecting
maps on the present faces, omitting a filler of the unknown middle rings.
-/

@[expose] public section

noncomputable section

universe u

open KaehlerDifferential

namespace RingHom.SquareZeroExtension

variable {A₁' A₁ B₁ N₁ : Type u} {A₂' A₂ B₂ N₂ : Type u}
variable [CommRing A₁'] [CommRing A₁] [CommRing B₁] [Algebra A₁ B₁]
variable [CommRing A₂'] [CommRing A₂] [CommRing B₂] [Algebra A₂ B₂]
variable [AddCommGroup N₁] [Module B₁ N₁] [Module A₁ N₁] [IsScalarTower A₁ B₁ N₁]
variable [AddCommGroup N₂] [Module B₂ N₂] [Module A₂ N₂] [IsScalarTower A₂ B₂ N₂]

/-- The map on square-zero kernels induced by a commutative square of ring homomorphisms. -/
def kerMapOfHoms {R' R S' S : Type u} [CommRing R'] [CommRing R] [CommRing S'] [CommRing S]
    {πR : R' →+* R} [πR.IsSquareZeroExtension] {πS : S' →+* S} [πS.IsSquareZeroExtension]
    (f' : R' →+* S') (f : R →+* S) (hcomm : πS.comp f' = f.comp πR) :
    KernelModule πR →+ KernelModule πS where
  toFun x :=
    ofMem
      (Iff.mpr (mem_ker (f := πS) (r := f' x.1))
        ((DFunLike.congr_fun hcomm x.1).trans
          ((congrArg f x.2).trans (map_zero f))))
  map_zero' := sorry
  map_add' := sorry

/-- `kerMapOfHoms` acts by the source map of the square. -/
theorem kerMapOfHoms_apply {R' R S' S : Type u}
    [CommRing R'] [CommRing R] [CommRing S'] [CommRing S]
    {πR : R' →+* R} [πR.IsSquareZeroExtension] {πS : S' →+* S} [πS.IsSquareZeroExtension]
    (f' : R' →+* S') (f : R →+* S) (hcomm : πS.comp f' = f.comp πR) (x : KernelModule πR) :
    val (kerMapOfHoms f' f hcomm x) = f' (val x) := sorry

variable {π₁ : A₁' →+* A₁} [π₁.IsSquareZeroExtension]
variable {π₂ : A₂' →+* A₂} [π₂.IsSquareZeroExtension]
variable {c₁ : KernelModule π₁ →ₗ[A₁] N₁}
variable {c₂ : KernelModule π₂ →ₗ[A₂] N₂}

/-- A connecting diagram of two solutions of relative square-zero solutions, with the filler B'₁ → B'₂ omitted. -/
structure RelativeDiagram (S₁ : Solution (B := B₁) (N := N₁) π₁ c₁) (S₂ : Solution (B := B₂) (N := N₂) π₂ c₂) where
  /-- The map of square-zero source rings A'₁ →+* A'₂. -/
  t' : A₁' →+* A₂'
  /-- The map of base rings A₁ →+* A₂. -/
  t : A₁ →+* A₂
  /-- The map of algebras B₁ →+* B₂. -/
  g : B₁ →+* B₂
  /-- The additive map of kernels N₁ → N₂. -/
  ν : N₁ →+ N₂
  /-- ν is linear over B₁ after restriction along g. -/
  map_smul_ν : ∀ (b : B₁) (n : N₁), ν (b • n) = g b • ν n
  /-- The base square of square-zero extensions commutes. -/
  comm_base : π₂.comp t' = t.comp π₁
  /-- The algebra square commutes. -/
  comm_alg : g.comp (algebraMap A₁ B₁) = (algebraMap A₂ B₂).comp t
  /-- The left kernel square involving c₁, c₂, and ν commutes. -/
  comm_kernel : ∀ x : KernelModule π₁,
    ν (c₁ x) = c₂ (kerMapOfHoms t' t comm_base x)

namespace RelativeDiagram

/-- Assemble a relative diagram from connecting maps and the three face equalities. -/
def of (S₁ : Solution (B := B₁) (N := N₁) π₁ c₁) (S₂ : Solution (B := B₂) (N := N₂) π₂ c₂)
    (t' : A₁' →+* A₂') (t : A₁ →+* A₂) (g : B₁ →+* B₂) (ν : N₁ →+ N₂)
    (map_smul_ν : ∀ (b : B₁) (n : N₁), ν (b • n) = g b • ν n)
    (comm_base : π₂.comp t' = t.comp π₁)
    (comm_alg : g.comp (algebraMap A₁ B₁) = (algebraMap A₂ B₂).comp t)
    (comm_kernel : ∀ x : KernelModule π₁,
      ν (c₁ x) = c₂ (kerMapOfHoms t' t comm_base x)) :
    RelativeDiagram S₁ S₂ where
  t' := t'
  t := t
  g := g
  ν := ν
  map_smul_ν := map_smul_ν
  comm_base := comm_base
  comm_alg := comm_alg
  comm_kernel := comm_kernel

variable {S₁ : Solution (B := B₁) (N := N₁) π₁ c₁} {S₂ : Solution (B := B₂) (N := N₂) π₂ c₂}

/-- The present ring-homomorphism faces of a relative diagram commute. -/
theorem spec (D : RelativeDiagram S₁ S₂) :
    π₂.comp D.t' = D.t.comp π₁ ∧
      D.g.comp (algebraMap A₁ B₁) = (algebraMap A₂ B₂).comp D.t := sorry

/-- The left kernel square of a relative diagram commutes. -/
theorem spec_kernel (D : RelativeDiagram S₁ S₂) (x : KernelModule π₁) :
    D.ν (c₁ x) = c₂ (kerMapOfHoms D.t' D.t D.comm_base x) := sorry

variable (D : RelativeDiagram S₁ S₂)

/-- N₂ as a B₁-module by restriction of scalars along the connecting map g. -/
@[reducible] def moduleRestrict : Module B₁ N₂ :=
  Module.compHom N₂ D.g

/-- N₂ as an A₁-module through B₁ → B₂. -/
@[reducible] def moduleRestrictA : Module A₁ N₂ :=
  Module.compHom N₂ (D.g.comp (algebraMap A₁ B₁))

/-- The restricted actions of A₁ and B₁ on N₂ form a scalar tower. -/
theorem isScalarTowerRestrict :
    -- Local instance justification (noncanonical choice): the B₁-action on N₂ is restriction along D.g.
    letI := moduleRestrict D
    -- Local instance justification (noncanonical choice): the A₁-action on N₂ is restriction along D.g.comp (algebraMap A₁ B₁).
    letI := moduleRestrictA D
    IsScalarTower A₁ B₁ N₂ := sorry

/-- The B₁-linear map N₁ →ₗ[B₁] N₂ packaged from the additive connecting map ν. -/
def νLinear :
    -- Local instance justification (noncanonical choice): the B₁-action on N₂ is restriction along D.g.
    letI := moduleRestrict D
    N₁ →ₗ[B₁] N₂ :=
  -- Local instance justification (noncanonical choice): the B₁-action on N₂ is restriction along D.g.
  letI := moduleRestrict D
  { toFun := D.ν
    map_add' := D.ν.map_add
    map_smul' := D.map_smul_ν }

/-- `νLinear` recovers the additive connecting map ν. -/
theorem νLinear_apply (n : N₁) : νLinear D n = D.ν n := sorry

/-- The restricted differential Hom space attached to a relative diagram. -/
abbrev Differentials : Type u :=
  -- Local instance justification (noncanonical choice): the differential codomain is restricted along D.g.
  letI := moduleRestrict D
  Ω[B₁⁄A₁] →ₗ[B₁] N₂

end RelativeDiagram

variable {S₁ : Solution (B := B₁) (N := N₁) π₁ c₁} {S₂ : Solution (B := B₂) (N := N₂) π₂ c₂}

/-- A ring map B'₁ → B'₂ fitting into a relative diagram. -/
structure FittingMap (D : RelativeDiagram S₁ S₂) where
  /-- The filler homomorphism B'₁ →+* B'₂. -/
  hom :
    -- Local instance justification (proof-local temporary data): bundled `S₁.commRing` is not globally registered on the structure Solution.
    letI := S₁.commRing
    -- Local instance justification (proof-local temporary data): bundled `S₂.commRing` is not globally registered on the structure Solution.
    letI := S₂.commRing
    S₁.carrier →+* S₂.carrier
  /-- The filler is compatible with the projections to B₁ and B₂. -/
  comm_toB :
    -- Local instance justification (proof-local temporary data): bundled `S₁.commRing` is not globally registered on the structure Solution.
    letI := S₁.commRing
    -- Local instance justification (proof-local temporary data): bundled `S₂.commRing` is not globally registered on the structure Solution.
    letI := S₂.commRing
    S₂.toB.comp hom = D.g.comp S₁.toB
  /-- The filler is compatible with the structure maps from A'₁ and A'₂. -/
  comm_fromA' :
    -- Local instance justification (proof-local temporary data): bundled `S₁.commRing` is not globally registered on the structure Solution.
    letI := S₁.commRing
    -- Local instance justification (proof-local temporary data): bundled `S₂.commRing` is not globally registered on the structure Solution.
    letI := S₂.commRing
    hom.comp S₁.fromA' = S₂.fromA'.comp D.t'
  /-- The filler induces the given connecting map ν on kernels. -/
  induces :
    -- Local instance justification (proof-local temporary data): bundled `S₁.commRing` is not globally registered on the structure Solution.
    letI := S₁.commRing
    -- Local instance justification (proof-local temporary data): bundled `S₂.commRing` is not globally registered on the structure Solution.
    letI := S₂.commRing
    -- Local instance justification (proof-local temporary data): bundled `S₁.isSquareZero` is not globally registered on the structure Solution.
    letI := S₁.isSquareZero
    -- Local instance justification (proof-local temporary data): bundled `S₂.isSquareZero` is not globally registered on the structure Solution.
    letI := S₂.isSquareZero
    ∀ x : KernelModule S₁.toB,
      S₂.kernelEquiv (kerMapOfHoms hom D.g comm_toB x) = D.ν (S₁.kernelEquiv x)

namespace FittingMap

/-- Assemble a fitting map from a ring homomorphism and the three compatibilities. -/
def of (D : RelativeDiagram S₁ S₂)
    (hom :
      -- Local instance justification (proof-local temporary data): bundled `S₁.commRing` is not globally registered on the structure Solution.
      letI := S₁.commRing
      -- Local instance justification (proof-local temporary data): bundled `S₂.commRing` is not globally registered on the structure Solution.
      letI := S₂.commRing
      S₁.carrier →+* S₂.carrier)
    (comm_toB :
      -- Local instance justification (proof-local temporary data): bundled `S₁.commRing` is not globally registered on the structure Solution.
      letI := S₁.commRing
      -- Local instance justification (proof-local temporary data): bundled `S₂.commRing` is not globally registered on the structure Solution.
      letI := S₂.commRing
      S₂.toB.comp hom = D.g.comp S₁.toB)
    (comm_fromA' :
      -- Local instance justification (proof-local temporary data): bundled `S₁.commRing` is not globally registered on the structure Solution.
      letI := S₁.commRing
      -- Local instance justification (proof-local temporary data): bundled `S₂.commRing` is not globally registered on the structure Solution.
      letI := S₂.commRing
      hom.comp S₁.fromA' = S₂.fromA'.comp D.t')
    (induces :
      -- Local instance justification (proof-local temporary data): bundled `S₁.commRing` is not globally registered on the structure Solution.
      letI := S₁.commRing
      -- Local instance justification (proof-local temporary data): bundled `S₂.commRing` is not globally registered on the structure Solution.
      letI := S₂.commRing
      -- Local instance justification (proof-local temporary data): bundled `S₁.isSquareZero` is not globally registered on the structure Solution.
      letI := S₁.isSquareZero
      -- Local instance justification (proof-local temporary data): bundled `S₂.isSquareZero` is not globally registered on the structure Solution.
      letI := S₂.isSquareZero
      ∀ x : KernelModule S₁.toB,
        S₂.kernelEquiv (kerMapOfHoms hom D.g comm_toB x) = D.ν (S₁.kernelEquiv x)) :
    FittingMap D where
  hom := hom
  comm_toB := comm_toB
  comm_fromA' := comm_fromA'
  induces := induces

/-- A fitting map is compatible with the projections to Bᵢ, the maps from A'ᵢ, and ν. -/
theorem spec (D : RelativeDiagram S₁ S₂) (φ : FittingMap D) :
    -- Local instance justification (proof-local temporary data): bundled `S₁.commRing` is not globally registered on the structure Solution.
    letI := S₁.commRing
    -- Local instance justification (proof-local temporary data): bundled `S₂.commRing` is not globally registered on the structure Solution.
    letI := S₂.commRing
    S₂.toB.comp φ.hom = D.g.comp S₁.toB ∧
      φ.hom.comp S₁.fromA' = S₂.fromA'.comp D.t' := sorry

/-- A fitting map induces the prescribed map on the square-zero kernels. -/
theorem spec_kernel (D : RelativeDiagram S₁ S₂) (φ : FittingMap D) :
    -- Local instance justification (proof-local temporary data): the kernel map has source carrier `S₁.carrier`.
    letI := S₁.commRing
    -- Local instance justification (proof-local temporary data): the kernel map has target carrier `S₂.carrier`.
    letI := S₂.commRing
    -- Local instance justification (proof-local temporary data): `KernelModule S₁.toB` uses the square-zero kernel structure stored in `S₁`.
    letI := S₁.isSquareZero
    -- Local instance justification (proof-local temporary data): `KernelModule S₂.toB` uses the square-zero kernel structure stored in `S₂`.
    letI := S₂.isSquareZero
    ∀ x : KernelModule S₁.toB,
      S₂.kernelEquiv (kerMapOfHoms φ.hom D.g φ.comm_toB x) = D.ν (S₁.kernelEquiv x) := sorry

/-- The difference of two fitting maps, evaluated on B'₁, lands in the kernel of B'₂ → B₂. -/
theorem sub_mem_ker (D : RelativeDiagram S₁ S₂) (φ φ' : FittingMap D)
    (x :
      -- Local instance justification (proof-local temporary data): bundled `S₁.commRing` is not globally registered on the structure Solution.
      letI := S₁.commRing
      S₁.carrier) :
    -- Local instance justification (proof-local temporary data): bundled `S₁.commRing` is not globally registered on the structure Solution.
    letI := S₁.commRing
    -- Local instance justification (proof-local temporary data): bundled `S₂.commRing` is not globally registered on the structure Solution.
    letI := S₂.commRing
    S₂.toB (φ'.hom x - φ.hom x) = 0 := sorry

/-- The action of Hom_{B₁}(Ω[B₁⁄A₁], N₂) on fitting maps, sending φ to φ + D. -/
def perturb (D : RelativeDiagram S₁ S₂)
    (α : RelativeDiagram.Differentials D)
    (φ : FittingMap D) : FittingMap D :=
  -- Local instance justification (noncanonical choice): the B₁-action on N₂ is restriction along D.g.
  letI := RelativeDiagram.moduleRestrict D
  { hom :=
      -- Local instance justification (proof-local temporary data): bundled `S₁.commRing` is not globally registered on the structure Solution.
      letI := S₁.commRing
      -- Local instance justification (proof-local temporary data): bundled `S₂.commRing` is not globally registered on the structure Solution.
      letI := S₂.commRing
      { toFun := fun x ↦
          -- Local instance justification (proof-local temporary data): bundled `S₂.isSquareZero` is not globally registered on the structure Solution.
          letI := S₂.isSquareZero
          φ.hom x + Solution.inclusion π₂ c₂ S₂ (α (KaehlerDifferential.D A₁ B₁ (S₁.toB x)))
        map_one' := sorry
        map_mul' := sorry
        map_zero' := sorry
        map_add' := sorry }
    comm_toB := sorry
    comm_fromA' := sorry
    induces := sorry }

/-- `perturb` adds the derivation associated to α through the square-zero kernel of B'₂. -/
theorem perturb_hom (D : RelativeDiagram S₁ S₂)
    (α : RelativeDiagram.Differentials D)
    (φ : FittingMap D)
    (x :
      -- Local instance justification (proof-local temporary data): bundled `S₁.commRing` is not globally registered on the structure Solution.
      letI := S₁.commRing
      S₁.carrier) :
    -- Local instance justification (proof-local temporary data): bundled `S₁.commRing` is not globally registered on the structure Solution.
    letI := S₁.commRing
    -- Local instance justification (proof-local temporary data): bundled `S₂.commRing` is not globally registered on the structure Solution.
    letI := S₂.commRing
    -- Local instance justification (proof-local temporary data): bundled `S₂.isSquareZero` is not globally registered on the structure Solution.
    letI := S₂.isSquareZero
    (perturb D α φ).hom x =
      φ.hom x + Solution.inclusion π₂ c₂ S₂ (α (KaehlerDifferential.D A₁ B₁ (S₁.toB x))) := sorry

/-- The Hom_{B₁}(Ω[B₁⁄A₁], N₂) measuring the difference of two fitting maps. -/
def diff (D : RelativeDiagram S₁ S₂) (φ φ' : FittingMap D) :
    RelativeDiagram.Differentials D :=
  -- Local instance justification (noncanonical choice): the B₁-action on N₂ is restriction along D.g.
  letI := RelativeDiagram.moduleRestrict D
  -- Local instance justification (noncanonical choice): the A₁-action on N₂ is restriction along D.g.comp (algebraMap A₁ B₁).
  letI := RelativeDiagram.moduleRestrictA D
  -- Local instance justification (noncanonical choice): the A₁/B₁ actions on N₂ form a tower through D.g.
  letI := RelativeDiagram.isScalarTowerRestrict D
  (linearMapEquivDerivation A₁ B₁).symm
    { toFun := fun b ↦
        -- Local instance justification (proof-local temporary data): bundled `S₁.commRing` is not globally registered on the structure Solution.
        letI := S₁.commRing
        -- Local instance justification (proof-local temporary data): bundled `S₂.commRing` is not globally registered on the structure Solution.
        letI := S₂.commRing
        -- Local instance justification (proof-local temporary data): bundled `S₁.isSquareZero` is not globally registered on the structure Solution.
        letI := S₁.isSquareZero
        -- Local instance justification (proof-local temporary data): bundled `S₂.isSquareZero` is not globally registered on the structure Solution.
        letI := S₂.isSquareZero
        let y := Function.surjInv S₁.isSquareZero.surjective b
        S₂.kernelEquiv
          (ofMem (Iff.mpr (mem_ker (f := S₂.toB) (r := φ'.hom y - φ.hom y))
            (sub_mem_ker D φ φ' y)))
      map_add' := sorry
      map_smul' := sorry
      map_one_eq_zero' := sorry
      leibniz' := sorry }

/-- The differential of two fitting maps evaluates to their pointwise difference. -/
theorem diff_apply (D : RelativeDiagram S₁ S₂) (φ φ' : FittingMap D)
    (x : S₁.carrier) :
    -- Local instance justification (proof-local temporary data): the pointwise difference uses the front carrier ring.
    letI := S₁.commRing
    -- Local instance justification (proof-local temporary data): the pointwise difference uses the back carrier ring.
    letI := S₂.commRing
    Solution.inclusion π₂ c₂ S₂ (diff D φ φ' (KaehlerDifferential.D A₁ B₁ (S₁.toB x))) =
      φ'.hom x - φ.hom x := sorry

/-- `diff` is the unique Hom(Ω, N₂) comparing two fitting maps, as a B₁-linear map. -/
theorem diff_spec (D : RelativeDiagram S₁ S₂) (φ φ' : FittingMap D) :
    perturb D (diff D φ φ') φ = φ' := sorry

/-- Perturbation by the zero differential leaves a fitting map unchanged. -/
theorem perturb_zero (D : RelativeDiagram S₁ S₂) (φ : FittingMap D) :
    perturb D 0 φ = φ := sorry

/-- Perturbation is additive in the differential. -/
theorem perturb_add (D : RelativeDiagram S₁ S₂)
    (α β : RelativeDiagram.Differentials D)
    (φ : FittingMap D) :
    perturb D (α + β) φ = perturb D α (perturb D β φ) := sorry

end FittingMap

/-- Every pair of fillers differs by a unique linear perturbation. -/
theorem fittingMap_principalHomogeneous (D : RelativeDiagram S₁ S₂)
    (φ φ' : FittingMap D) :
    ∃! α : RelativeDiagram.Differentials D, FittingMap.perturb D α φ = φ' := sorry

end SquareZeroExtension

end RingHom
