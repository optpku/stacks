/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Square-zero extensions of commutative rings

This file separates the canonical property of a square-zero surjection and
the annihilator determined by its kernel from the noncanonical choice of a
kernel generator.  Generator-dependent declarations provide comparison maps
and compatibility aliases for deformation arguments.

@stack 09PS
-/

universe u v w

namespace RingHom

variable {R' : Type u} {R : Type v} [CommRing R'] [CommRing R]

/-- A ring homomorphism is a square-zero extension when it is surjective and
the square of its kernel vanishes. -/
@[stacks 09PS "square-zero extension"]
class IsSquareZeroExtension (f : R' →+* R) : Prop where
  /-- A square-zero extension is surjective. -/
  surjective : Function.Surjective f
  /-- The kernel ideal has square zero. -/
  ker_sq_eq_bot : RingHom.ker f ^ 2 = ⊥

namespace IsSquareZeroExtension

/-- The defining conditions for a square-zero extension. -/
theorem spec (f : R' →+* R) [h : f.IsSquareZeroExtension] :
    Function.Surjective f ∧ RingHom.ker f ^ 2 = ⊥ := sorry

/-- The kernel ideal of a square-zero extension is nilpotent. -/
@[stacks 09PS "nilpotent kernel of a square-zero extension"]
theorem ker_isNilpotent (f : R' →+* R) [f.IsSquareZeroExtension] :
    IsNilpotent (RingHom.ker f) := sorry

end IsSquareZeroExtension

namespace SquareZeroExtension

/-- The annihilator in the source ring of the kernel of a square-zero
extension. -/
@[stacks 09PS "source kernel annihilator"]
def sourceKernelAnnihilator (f : R' →+* R) [f.IsSquareZeroExtension] : Ideal R' :=
  (RingHom.ker f).annihilator

/-- The annihilator of the kernel of a square-zero extension, descended to
the target ring. -/
@[stacks 09PS "kernel annihilator"]
def kernelAnnihilator (f : R' →+* R) [f.IsSquareZeroExtension] : Ideal R :=
  (sourceKernelAnnihilator f).map f

/-- The kernel of a square-zero extension is contained in its source
annihilator. -/
theorem ker_le_sourceKernelAnnihilator (f : R' →+* R) [f.IsSquareZeroExtension] :
    RingHom.ker f ≤ sourceKernelAnnihilator f := sorry

/-- Pulling the descended kernel annihilator back to the source recovers the
source kernel annihilator. -/
@[simp]
theorem comap_kernelAnnihilator (f : R' →+* R) [f.IsSquareZeroExtension] :
    (kernelAnnihilator f).comap f = sourceKernelAnnihilator f := sorry

/-- Membership in the source kernel annihilator means annihilating every
element of the kernel. -/
theorem mem_sourceKernelAnnihilator_iff (f : R' →+* R) [f.IsSquareZeroExtension]
    (x : R') :
    x ∈ sourceKernelAnnihilator f ↔
      ∀ y : R', y ∈ RingHom.ker f → x * y = 0 := sorry

/-- Membership in the descended kernel annihilator can be checked on every
lift and every element of the kernel. -/
theorem mem_kernelAnnihilator_iff (f : R' →+* R) [f.IsSquareZeroExtension]
    (r : R) :
    r ∈ kernelAnnihilator f ↔
      ∀ x : R', f x = r → ∀ y : R', y ∈ RingHom.ker f → x * y = 0 := sorry

/-- The source ring modulo the annihilator of the square-zero kernel. -/
@[stacks 09PS "source kernel annihilator quotient"]
abbrev sourceKernelQuotient (f : R' →+* R) [f.IsSquareZeroExtension] :=
  R' ⧸ sourceKernelAnnihilator f

/-- The quotient ring map from the source kernel-annihilator quotient to the
corresponding quotient of the target. -/
@[stacks 09PS "source-to-target kernel annihilator quotient map"]
def sourceQuotientMap (f : R' →+* R) [f.IsSquareZeroExtension] :
    sourceKernelQuotient f →+* R ⧸ kernelAnnihilator f :=
  Ideal.quotientMap (kernelAnnihilator f) f Ideal.le_comap_map

/-- The source-to-target quotient map sends the class of `x` to the class of
`f x`. -/
@[simp]
theorem sourceQuotientMap_apply_mk (f : R' →+* R) [f.IsSquareZeroExtension]
    (x : R') :
    sourceQuotientMap f (Ideal.Quotient.mk (sourceKernelAnnihilator f) x) =
      Ideal.Quotient.mk (kernelAnnihilator f) (f x) := sorry

/-- The source-to-target kernel-annihilator quotient map is injective. -/
theorem sourceQuotientMap_injective (f : R' →+* R) [f.IsSquareZeroExtension] :
    Function.Injective (sourceQuotientMap f) := sorry

/-- The source-to-target kernel-annihilator quotient map is surjective. -/
theorem sourceQuotientMap_surjective (f : R' →+* R) [f.IsSquareZeroExtension] :
    Function.Surjective (sourceQuotientMap f) := sorry

/-- The source-to-target kernel-annihilator quotient map is bijective. -/
theorem sourceQuotientMap_bijective (f : R' →+* R) [f.IsSquareZeroExtension] :
    Function.Bijective (sourceQuotientMap f) := sorry

section Algebra

variable (f : R' →+* R) [f.IsSquareZeroExtension]
variable (A : Type w) [CommRing A] [Algebra R A]

/-- The extension to an `R`-algebra of the intrinsic kernel annihilator. -/
@[stacks 09PS "extended kernel annihilator"]
abbrev kernelAnnihilatorIdeal : Ideal A :=
  (kernelAnnihilator f).map (algebraMap R A)

/-- The quotient of an `R`-algebra by the extended intrinsic kernel
annihilator. -/
@[stacks 09PS "kernel annihilator quotient"]
abbrev kernelAnnihilatorQuotient :=
  A ⧸ kernelAnnihilatorIdeal f A

end Algebra

/-- A chosen generator of the kernel of a square-zero extension.  Generator
choices are explicit because they are generally not canonical. -/
@[stacks 09PS "principal square-zero extension"]
structure Generator (f : R' →+* R) [f.IsSquareZeroExtension] where
  /-- The chosen element generating the kernel. -/
  element : R'
  /-- The kernel is the principal ideal generated by `element`. -/
  ker_eq_span : RingHom.ker f = Ideal.span ({element} : Set R')

namespace Generator

variable {f : R' →+* R} [f.IsSquareZeroExtension]

/-- A kernel generator specified by an element whose singleton span equals the kernel. -/
def ofElement (element : R')
    (ker_eq_span : RingHom.ker f = Ideal.span ({element} : Set R')) : Generator f where
  element := element
  ker_eq_span := ker_eq_span

/-- The annihilator of a chosen kernel generator in the source ring. -/
def sourceAnnihilator (g : Generator f) : Ideal R' :=
  (⊥ : Ideal R').colon {g.element}

/-- The annihilator of a chosen kernel generator, descended to the target of
the square-zero extension. -/
def annihilator (g : Generator f) : Ideal R :=
  g.sourceAnnihilator.map f

/-- The source annihilator defined from a kernel generator agrees with the
intrinsic annihilator of the kernel. -/
@[simp]
theorem sourceAnnihilator_eq_sourceKernelAnnihilator (g : Generator f) :
    g.sourceAnnihilator = sourceKernelAnnihilator f := sorry

/-- The descended annihilator defined from a kernel generator agrees with
the intrinsic kernel annihilator. -/
@[simp, stacks 09PS "generator annihilator is intrinsic"]
theorem annihilator_eq_kernelAnnihilator (g : Generator f) :
    g.annihilator = kernelAnnihilator f := sorry

/-- The chosen generator belongs to the kernel. -/
theorem element_mem_ker (g : Generator f) : g.element ∈ RingHom.ker f := sorry

/-- Multiplying an arbitrary source element by the chosen generator gives an
element of the kernel. -/
theorem mul_element_mem_ker (g : Generator f) (x : R') :
    x * g.element ∈ RingHom.ker f := sorry

/-- Multiplication by a chosen kernel generator, with codomain restricted to
the kernel. -/
@[stacks 09PS "multiplication onto a principal square-zero kernel"]
def toKernel (g : Generator f) : R' →ₗ[R'] RingHom.ker f :=
  LinearMap.codRestrict (RingHom.ker f) (LinearMap.mulRight R' g.element)
    g.mul_element_mem_ker

/-- The multiplication map to the kernel sends `x` to
`x * g.element`. -/
@[simp]
theorem toKernel_apply (g : Generator f) (x : R') :
    (g.toKernel x : R') = x * g.element := sorry

/-- The kernel of multiplication by a chosen kernel generator is the
intrinsic source kernel annihilator. -/
theorem ker_toKernel (g : Generator f) :
    LinearMap.ker g.toKernel = sourceKernelAnnihilator f := sorry

/-- Multiplication by a chosen kernel generator surjects onto the kernel. -/
theorem toKernel_surjective (g : Generator f) :
    Function.Surjective g.toKernel := sorry

/-- The explicit linear map from the intrinsic source annihilator quotient
to the kernel, induced by multiplication by a chosen generator. -/
@[stacks 09PS "source annihilator quotient maps to kernel"]
def sourceQuotientToKernel (g : Generator f) :
    sourceKernelQuotient f →ₗ[R'] RingHom.ker f :=
  (sourceKernelAnnihilator f).liftQ g.toKernel (le_of_eq g.ker_toKernel.symm)

/-- The quotient-to-kernel map sends the class of `x` to
`x * g.element`. -/
@[simp]
theorem sourceQuotientToKernel_apply_mk (g : Generator f) (x : R') :
    (g.sourceQuotientToKernel
      (Ideal.Quotient.mk (sourceKernelAnnihilator f) x) : R') =
        x * g.element := sorry

/-- The quotient-to-kernel map induced by a generator is bijective. -/
theorem sourceQuotientToKernel_bijective (g : Generator f) :
    Function.Bijective g.sourceQuotientToKernel := sorry

/-- Every element of the kernel annihilates the chosen generator. -/
theorem mul_element_eq_zero_of_mem_ker
    (g : Generator f) {x : R'} (hx : x ∈ RingHom.ker f) :
    x * g.element = 0 := sorry

/-- Membership in the source annihilator is multiplication by the chosen
generator being zero. -/
theorem mem_sourceAnnihilator_iff (g : Generator f) (x : R') :
    x ∈ g.sourceAnnihilator ↔ x * g.element = 0 := sorry

/-- Membership in the descended annihilator can be checked on every lift to
the source ring. -/
theorem mem_annihilator_iff (g : Generator f) (r : R) :
    r ∈ g.annihilator ↔
      ∀ x : R', f x = r → x * g.element = 0 := sorry

section Algebra

variable (g : Generator f) (A : Type w) [CommRing A] [Algebra R A]

include g

/-- Extending the generator-defined annihilator gives the intrinsic
compatibility annihilator ideal. -/
@[simp]
theorem map_annihilator_eq :
    g.annihilator.map (algebraMap R A) = kernelAnnihilatorIdeal f A := sorry

end Algebra

end Generator

end SquareZeroExtension

end RingHom
