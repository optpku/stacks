module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.RingTheory.RingHom.SquareZero

/-!
# Square-zero thickenings over a fixed commutative ring

A morphism of square-zero extensions of a fixed commutative ring `A` is a ring
map over `A`. The kernels of the structure maps are canonically `A`-modules,
and a short exact sequence of such morphisms is exactness of `0 → I3 → I2 → I1 → 0`.
In that case the first thickening is canonically the trivial square-zero
extension `TrivSqZeroExt A I1`.
-/

@[expose] public section

open CategoryTheory TrivSqZeroExt

noncomputable section

universe u

namespace AlgebraicGeometry.Deformation

variable {A A' B' C' A1' A2' A3' : Type u}
variable [CommRing A] [CommRing A'] [CommRing B'] [CommRing C']
variable [CommRing A1'] [CommRing A2'] [CommRing A3']

/-- Opposite scalars on an `A`-module, using that `A` is commutative. -/
instance (priority := 100) instModuleOp {M : Type u} [AddCommGroup M] [Module A M] :
    Module Aᵐᵒᵖ M :=
  Module.compHom M ((RingHom.id A).fromOpposite mul_comm)

/-- Scalar actions of `A` and `Aᵐᵒᵖ` agree on an `A`-module. -/
instance (priority := 100) instIsCentralScalar {M : Type u} [AddCommGroup M] [Module A M] :
    IsCentralScalar A M where
  op_smul_eq_smul _ _ := rfl

/-- The identity map of a commutative ring is a square-zero extension. -/
instance instIsSquareZeroExtension_id : (RingHom.id A).IsSquareZeroExtension where
  surjective := Function.surjective_id
  ker_sq_eq_bot := sorry

/-- The coefficient projection of a trivial square-zero extension is a
square-zero extension. -/
instance instIsSquareZeroExtension_fstHom {M : Type u} [AddCommGroup M] [Module A M] :
    (fstHom A A M).toRingHom.IsSquareZeroExtension := sorry

/-- A morphism of square-zero extensions of a fixed commutative ring `A`. -/
abbrev Hom (π : A' →+* A) (σ : B' →+* A) [π.IsSquareZeroExtension]
    [σ.IsSquareZeroExtension] := {f : A' →+* B' // σ.comp f = π}

/-- The underlying ring homomorphism of a morphism of square-zero extensions. -/
def Hom.hom {π : A' →+* A} {σ : B' →+* A} [π.IsSquareZeroExtension]
    [σ.IsSquareZeroExtension] (f : Hom π σ) : A' →+* B' := f.1

/-- The commuting condition of a morphism of square-zero extensions. -/
theorem Hom.comm {π : A' →+* A} {σ : B' →+* A} [π.IsSquareZeroExtension]
    [σ.IsSquareZeroExtension] (f : Hom π σ) : σ.comp f.hom = π := f.2

/-- Package a ring homomorphism over `A` as a morphism of square-zero
extensions. -/
def Hom.of {π : A' →+* A} {σ : B' →+* A} [π.IsSquareZeroExtension]
    [σ.IsSquareZeroExtension] (f : A' →+* B') (hf : σ.comp f = π) : Hom π σ where
  val := f
  property := hf

/-- The identity morphism of a square-zero extension of `A`. -/
def Hom.id (π : A' →+* A) [π.IsSquareZeroExtension] : Hom π π where
  val := RingHom.id A'
  property := RingHom.comp_id π

/-- Composition of morphisms of square-zero extensions of `A`. -/
def Hom.comp {π : A' →+* A} {σ : B' →+* A} {τ : C' →+* A} [π.IsSquareZeroExtension]
    [σ.IsSquareZeroExtension] [τ.IsSquareZeroExtension] (f : Hom π σ) (g : Hom σ τ) :
    Hom π τ := Hom.of (g.hom.comp f.hom) sorry

/-- The underlying ring homomorphism of `Hom.of` is the given map. -/
theorem Hom.of_hom {π : A' →+* A} {σ : B' →+* A} [π.IsSquareZeroExtension]
    [σ.IsSquareZeroExtension] (f : A' →+* B') (hf : σ.comp f = π) :
    (Hom.of f hf).hom = f := rfl

/-- The identity morphism has underlying identity ring homomorphism. -/
theorem Hom.id_hom (π : A' →+* A) [π.IsSquareZeroExtension] :
    (Hom.id π).hom = RingHom.id A' := rfl

/-- Composition of morphisms of square-zero extensions composes the underlying
ring homomorphisms. -/
theorem Hom.comp_hom {π : A' →+* A} {σ : B' →+* A} {τ : C' →+* A}
    [π.IsSquareZeroExtension] [σ.IsSquareZeroExtension] [τ.IsSquareZeroExtension]
    (f : Hom π σ) (g : Hom σ τ) : (Hom.comp f g).hom = g.hom.comp f.hom := rfl

/-- A morphism of square-zero extensions lies over `A`. -/
theorem Hom.spec {π : A' →+* A} {σ : B' →+* A} [π.IsSquareZeroExtension]
    [σ.IsSquareZeroExtension] (f : Hom π σ) : σ.comp f.hom = π := f.comm

/-- The coefficient projection composed with the canonical inclusion of `A`
into `TrivSqZeroExt A M` is the identity. -/
theorem fstHom_comp_inlHom (M : Type u) [AddCommGroup M] [Module A M] :
    (fstHom A A M).toRingHom.comp (inlHom A M) = RingHom.id A := sorry

/-- The canonical inclusion of `A` into the trivial square-zero extension
`TrivSqZeroExt A M`, as a morphism of square-zero thickenings over `A`. -/
def Hom.inl (M : Type u) [AddCommGroup M] [Module A M] :
    Hom (RingHom.id A) (fstHom A A M).toRingHom :=
  Hom.of (inlHom A M) (fstHom_comp_inlHom M)

/-- The kernel of a square-zero extension `π : A' →+* A`, viewed as the
`A`-module of infinitesimal thickenings. -/
abbrev kernelModule (π : A' →+* A) [π.IsSquareZeroExtension] : Type u :=
  RingHom.ker π

/-- An element of `A'` lies in the kernel module iff it vanishes under `π`. -/
theorem mem_kernelModule_iff (π : A' →+* A) [π.IsSquareZeroExtension] {x : A'} :
    (∃ y : kernelModule π, y.val = x) ↔ π x = 0 := sorry

/-- The kernel of a square-zero extension of `A` is an `A`-module, by
restricting scalars along `A' ⧸ ker π ≃+* A`. -/
instance instModule_kernelModule {π : A' →+* A} [hπ : π.IsSquareZeroExtension] :
    Module A (kernelModule π) where
  smul a x :=
    ⟨Quotient.out ((RingHom.quotientKerEquivOfSurjective hπ.surjective).symm a) * x.val,
      Ideal.mul_mem_left (RingHom.ker π) _ x.property⟩
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- A morphism of square-zero extensions sends the source kernel into the
target kernel. -/
theorem kernelMap_mem {π : A' →+* A} {σ : B' →+* A} [π.IsSquareZeroExtension]
    [σ.IsSquareZeroExtension] (f : Hom π σ) (x : kernelModule π) :
    f.hom x.val ∈ RingHom.ker σ := sorry

/-- The `A`-linear map on kernels induced by a morphism of square-zero
extensions of `A`. -/
def kernelMap {π : A' →+* A} {σ : B' →+* A} [π.IsSquareZeroExtension]
    [σ.IsSquareZeroExtension] (f : Hom π σ) :
    kernelModule π →ₗ[A] kernelModule σ where
  toFun x := ⟨f.hom x.val, kernelMap_mem f x⟩
  map_add' := sorry
  map_smul' := sorry

/-- `kernelMap` acts by the underlying ring homomorphism. -/
theorem kernelMap_apply {π : A' →+* A} {σ : B' →+* A} [π.IsSquareZeroExtension]
    [σ.IsSquareZeroExtension] (f : Hom π σ) (x : kernelModule π) :
    (kernelMap f x).val = f.hom x.val := sorry

/-- The diagram `I3 → I2 → I1` of kernels associated to a composable pair of
morphisms of square-zero extensions of `A`. -/
def kernelComplex {π1 : A1' →+* A} {π2 : A2' →+* A} {π3 : A3' →+* A}
    [π1.IsSquareZeroExtension] [π2.IsSquareZeroExtension] [π3.IsSquareZeroExtension]
    (f21 : Hom π2 π1) (f32 : Hom π3 π2)
    (hzero : ModuleCat.ofHom (kernelMap f32) ≫ ModuleCat.ofHom (kernelMap f21) = 0) :
    ShortComplex (ModuleCat.{u} A) where
  X₁ := ModuleCat.of A (kernelModule π3)
  X₂ := ModuleCat.of A (kernelModule π2)
  X₃ := ModuleCat.of A (kernelModule π1)
  f := ModuleCat.ofHom (kernelMap f32)
  g := ModuleCat.ofHom (kernelMap f21)
  zero := hzero

/-- A short exact sequence of square-zero extensions of a fixed commutative
ring `A` is a composable pair whose induced kernel sequence
`0 → I3 → I2 → I1 → 0` is short exact. -/
class IsShortExact {π1 : A1' →+* A} {π2 : A2' →+* A} {π3 : A3' →+* A}
    [π1.IsSquareZeroExtension] [π2.IsSquareZeroExtension] [π3.IsSquareZeroExtension]
    (f21 : Hom π2 π1) (f32 : Hom π3 π2) : Prop where
  /-- The induced maps on kernels compose to zero. -/
  kernel_zero : ModuleCat.ofHom (kernelMap f32) ≫ ModuleCat.ofHom (kernelMap f21) = 0
  /-- The induced sequence of kernels is short exact. -/
  kernel_shortExact : (kernelComplex f21 f32 kernel_zero).ShortExact

/-- The split sequence `0 → 0 → M → M → 0` associated with
`A → TrivSqZeroExt A M → TrivSqZeroExt A M`, as a short exact sequence of
square-zero extensions of `A`. -/
instance instIsShortExact_trivial {M : Type u} [AddCommGroup M] [Module A M] :
    IsShortExact (Hom.id (fstHom A A M).toRingHom) (Hom.inl M) where
  kernel_zero := sorry
  kernel_shortExact := sorry

namespace IsShortExact

/-- Exactness forces the composite `A3' → A1'` to vanish on `ker π3`. -/
theorem ker_third_le_ker_comp {π1 : A1' →+* A} {π2 : A2' →+* A} {π3 : A3' →+* A}
    [π1.IsSquareZeroExtension] [π2.IsSquareZeroExtension] [π3.IsSquareZeroExtension]
    (f21 : Hom π2 π1) (f32 : Hom π3 π2) [IsShortExact f21 f32] :
    RingHom.ker π3 ≤ RingHom.ker (f21.hom.comp f32.hom) := sorry

/-- A short exact sequence of square-zero extensions lies over `A` and has
short exact kernel sequence together with the induced factorization condition. -/
theorem spec {π1 : A1' →+* A} {π2 : A2' →+* A} {π3 : A3' →+* A}
    [π1.IsSquareZeroExtension] [π2.IsSquareZeroExtension] [π3.IsSquareZeroExtension]
    (f21 : Hom π2 π1) (f32 : Hom π3 π2) [h : IsShortExact f21 f32] :
    π1.comp f21.hom = π2 ∧
      π2.comp f32.hom = π3 ∧
      (ModuleCat.ofHom (kernelMap f32) ≫ ModuleCat.ofHom (kernelMap f21) = 0) ∧
      (kernelComplex f21 f32 h.kernel_zero).ShortExact ∧
      RingHom.ker π3 ≤ RingHom.ker (f21.hom.comp f32.hom) := sorry

/-- Short exactness of a composable pair of square-zero extensions is exactness
of `0 → I3 → I2 → I1 → 0`. -/
theorem iff {π1 : A1' →+* A} {π2 : A2' →+* A} {π3 : A3' →+* A}
    [π1.IsSquareZeroExtension] [π2.IsSquareZeroExtension] [π3.IsSquareZeroExtension]
    (f21 : Hom π2 π1) (f32 : Hom π3 π2) :
    IsShortExact f21 f32 ↔
      ∃ hzero : ModuleCat.ofHom (kernelMap f32) ≫ ModuleCat.ofHom (kernelMap f21) = 0,
        (kernelComplex f21 f32 hzero).ShortExact := sorry

end IsShortExact

/-- The canonical section `A →+* A1'` of a short exact sequence of square-zero
extensions, obtained by factoring `A3' → A1'` through `A ≃ A3' ⧸ ker π3`. -/
def sectionHom {π1 : A1' →+* A} {π2 : A2' →+* A} {π3 : A3' →+* A}
    [π1.IsSquareZeroExtension] [π2.IsSquareZeroExtension]
    [hπ3 : π3.IsSquareZeroExtension]
    (f21 : Hom π2 π1) (f32 : Hom π3 π2) [IsShortExact f21 f32] : A →+* A1' :=
  (RingHom.kerLift (f21.hom.comp f32.hom)).comp
    ((Ideal.Quotient.factor (IsShortExact.ker_third_le_ker_comp f21 f32)).comp
      (RingHom.quotientKerEquivOfSurjective hπ3.surjective).symm.toRingHom)

/-- The canonical section is a section of `π1`. -/
theorem sectionHom_comp {π1 : A1' →+* A} {π2 : A2' →+* A} {π3 : A3' →+* A}
    [π1.IsSquareZeroExtension] [π2.IsSquareZeroExtension] [π3.IsSquareZeroExtension]
    (f21 : Hom π2 π1) (f32 : Hom π3 π2) [IsShortExact f21 f32] :
    π1.comp (sectionHom f21 f32) = RingHom.id A := sorry

/-- The composite `A3' → A1'` factors as `sectionHom ∘ π3`. -/
theorem sectionHom_factor {π1 : A1' →+* A} {π2 : A2' →+* A} {π3 : A3' →+* A}
    [π1.IsSquareZeroExtension] [π2.IsSquareZeroExtension] [π3.IsSquareZeroExtension]
    (f21 : Hom π2 π1) (f32 : Hom π3 π2) [IsShortExact f21 f32] :
    f21.hom.comp f32.hom = (sectionHom f21 f32).comp π3 := sorry

/-- Subtracting the canonical section of `π1` lands in the kernel. -/
theorem sub_section_mem_ker {π1 : A1' →+* A} {π2 : A2' →+* A} {π3 : A3' →+* A}
    [π1.IsSquareZeroExtension] [π2.IsSquareZeroExtension] [π3.IsSquareZeroExtension]
    (f21 : Hom π2 π1) (f32 : Hom π3 π2) [IsShortExact f21 f32] (a' : A1') :
    a' - sectionHom f21 f32 (π1 a') ∈ RingHom.ker π1 := sorry

/-- The canonical identification of the first thickening in a short exact
sequence of square-zero extensions with `TrivSqZeroExt A (kernelModule π1)`. -/
def trivSqZeroIso {π1 : A1' →+* A} {π2 : A2' →+* A} {π3 : A3' →+* A}
    [π1.IsSquareZeroExtension] [π2.IsSquareZeroExtension] [π3.IsSquareZeroExtension]
    (f21 : Hom π2 π1) (f32 : Hom π3 π2) [IsShortExact f21 f32] :
    A1' ≃+* TrivSqZeroExt A (kernelModule π1) where
  toFun a' :=
    inl (π1 a') + inr ⟨a' - sectionHom f21 f32 (π1 a'), sub_section_mem_ker f21 f32 a'⟩
  invFun x := sectionHom f21 f32 (fst x) + (snd x).val
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry
  map_add' := sorry

/-- The canonical isomorphism is compatible with the projections onto `A`. -/
theorem trivSqZeroIso_fst {π1 : A1' →+* A} {π2 : A2' →+* A} {π3 : A3' →+* A}
    [π1.IsSquareZeroExtension] [π2.IsSquareZeroExtension] [π3.IsSquareZeroExtension]
    (f21 : Hom π2 π1) (f32 : Hom π3 π2) [IsShortExact f21 f32] :
    (fstHom A A (kernelModule π1)).toRingHom.comp (trivSqZeroIso f21 f32).toRingHom =
      π1 := sorry

/-- The inverse isomorphism extends the canonical section along
`inlHom : A →+* TrivSqZeroExt A (kernelModule π1)`. -/
theorem trivSqZeroIso_symm_inl {π1 : A1' →+* A} {π2 : A2' →+* A} {π3 : A3' →+* A}
    [π1.IsSquareZeroExtension] [π2.IsSquareZeroExtension] [π3.IsSquareZeroExtension]
    (f21 : Hom π2 π1) (f32 : Hom π3 π2) [IsShortExact f21 f32] :
    (trivSqZeroIso f21 f32).symm.toRingHom.comp (inlHom A (kernelModule π1)) =
      sectionHom f21 f32 := sorry

end AlgebraicGeometry.Deformation
