/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Hom
public import ReasLib.Algebra.Homology.ComplexShape
public import ReasLib.Algebra.Homology.HomologicalComplex.Acyclic.Homology
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.Tactic.FinCases

@[expose] public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism.Hom

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : TwoPeriodicEndomorphism C}

/-- The kernel inclusion followed by the canonical map to the image is zero. -/
theorem kernelImageRow_zero (f : Hom K L) :
    kernel.ι f.toCochainComplexHom ≫
      Abelian.factorThruImage f.toCochainComplexHom = 0 := by
  rw [← cancel_mono (Abelian.image.ι f.toCochainComplexHom), Category.assoc,
    Abelian.image.fac, kernel.condition, zero_comp]

/-- The canonical short complex `kernel f ⟶ K ⟶ image f`. -/
noncomputable def kernelImageRow (f : Hom K L) :
    ShortComplex (CochainComplex C (ZMod 2)) :=
  ShortComplex.mk (kernel.ι f.toCochainComplexHom)
    (Abelian.factorThruImage f.toCochainComplexHom) (kernelImageRow_zero f)

/-- The canonical map from the image followed by the cokernel projection is zero. -/
theorem imageCokernelRow_zero (f : Hom K L) :
    Abelian.image.ι f.toCochainComplexHom ≫
      cokernel.π f.toCochainComplexHom = 0 := by
  exact kernel.condition (cokernel.π f.toCochainComplexHom)

/-- The canonical short complex `image f ⟶ L ⟶ cokernel f`. -/
noncomputable def imageCokernelRow (f : Hom K L) :
    ShortComplex (CochainComplex C (ZMod 2)) :=
  ShortComplex.mk (Abelian.image.ι f.toCochainComplexHom)
    (cokernel.π f.toCochainComplexHom) (imageCokernelRow_zero f)

/-- The kernel--source--image row of a periodic morphism is short exact. -/
theorem kernelImageRow_shortExact (f : Hom K L) : (kernelImageRow f).ShortExact where
  exact := (kernelImageRow f).exact_of_f_is_kernel
    (isKernelOfComp (Abelian.image.ι f.toCochainComplexHom) f.toCochainComplexHom
      (kernelIsKernel f.toCochainComplexHom) (kernelImageRow_zero f)
      (Abelian.image.fac f.toCochainComplexHom))
  mono_f := by
    change Mono (kernel.ι f.toCochainComplexHom)
    infer_instance
  epi_g := by
    change Epi (Abelian.factorThruImage f.toCochainComplexHom)
    infer_instance

/-- The image--target--cokernel row of a periodic morphism is short exact. -/
theorem imageCokernelRow_shortExact (f : Hom K L) : (imageCokernelRow f).ShortExact where
  exact := (imageCokernelRow f).exact_of_f_is_kernel
    (kernelIsKernel (cokernel.π f.toCochainComplexHom))
  mono_f := by
    change Mono (Abelian.image.ι f.toCochainComplexHom)
    infer_instance
  epi_g := by
    change Epi (cokernel.π f.toCochainComplexHom)
    infer_instance

/-- The differentials induced on the kernel complex of a periodic morphism vanish. -/
def KernelDifferentialsVanish (f : Hom K L) : Prop :=
  ∀ i j : ZMod 2, (kernel f.toCochainComplexHom).d i j = 0

/-- Vanishing of the kernel differential is equivalent to vanishing in the two periodic
degrees. -/
theorem kernelDifferentialsVanish_iff (f : Hom K L) :
    KernelDifferentialsVanish f ↔
      (kernel f.toCochainComplexHom).d 0 1 = 0 ∧
        (kernel f.toCochainComplexHom).d 1 0 = 0 := by
  constructor
  · intro h
    exact ⟨h 0 1, h 1 0⟩
  · rintro ⟨h₀, h₁⟩ i j
    fin_cases i <;> fin_cases j
    · exact (kernel f.toCochainComplexHom).shape 0 0 (by decide)
    · exact h₀
    · exact h₁
    · exact (kernel f.toCochainComplexHom).shape 1 1 (by decide)

/-- The differentials induced on the cokernel complex of a periodic morphism vanish. -/
def CokernelDifferentialsVanish (f : Hom K L) : Prop :=
  ∀ i j : ZMod 2, (cokernel f.toCochainComplexHom).d i j = 0

/-- Vanishing of the cokernel differential is equivalent to vanishing in the two periodic
degrees. -/
theorem cokernelDifferentialsVanish_iff (f : Hom K L) :
    CokernelDifferentialsVanish f ↔
      (cokernel f.toCochainComplexHom).d 0 1 = 0 ∧
        (cokernel f.toCochainComplexHom).d 1 0 = 0 := by
  constructor
  · intro h
    exact ⟨h 0 1, h 1 0⟩
  · rintro ⟨h₀, h₁⟩ i j
    fin_cases i <;> fin_cases j
    · exact (cokernel f.toCochainComplexHom).shape 0 0 (by decide)
    · exact h₀
    · exact h₁
    · exact (cokernel f.toCochainComplexHom).shape 1 1 (by decide)

/-- If every differential of a cochain complex vanishes, its homology in each degree is
canonically isomorphic to its term in that degree. -/
noncomputable def zeroDifferentialHomologyIso
    (A : CochainComplex C (ZMod 2)) (hA : ∀ i j, A.d i j = 0) (i : ZMod 2) :
    A.homology i ≅ A.X i :=
  A.isoHomologyι i ((ComplexShape.up (ZMod 2)).next i) rfl
      (hA i ((ComplexShape.up (ZMod 2)).next i)) ≪≫
    (A.pOpcyclesIso ((ComplexShape.up (ZMod 2)).prev i) i rfl
      (hA ((ComplexShape.up (ZMod 2)).prev i) i)).symm

/-- Homology of the cokernel complex, under the zero-differential hypothesis, identified with
the categorical cokernel of the underlying map. -/
noncomputable def cokernelHomologyIso (f : Hom K L) (hQ : CokernelDifferentialsVanish f)
    (i : ZMod 2) :
    (cokernel f.toCochainComplexHom).homology i ≅ cokernel f.hom :=
  zeroDifferentialHomologyIso (cokernel f.toCochainComplexHom) hQ i ≪≫
    PreservesCokernel.iso
      (HomologicalComplex.eval C (ComplexShape.up (ZMod 2)) i) f.toCochainComplexHom

/-- Homology of the kernel complex, under the zero-differential hypothesis, identified with
the categorical kernel of the underlying map. -/
noncomputable def kernelHomologyIso (f : Hom K L) (hK : KernelDifferentialsVanish f)
    (i : ZMod 2) :
    (kernel f.toCochainComplexHom).homology i ≅ kernel f.hom :=
  zeroDifferentialHomologyIso (kernel f.toCochainComplexHom) hK i ≪≫
    PreservesKernel.iso
      (HomologicalComplex.eval C (ComplexShape.up (ZMod 2)) i) f.toCochainComplexHom

/-- The canonical boundary isomorphism from `cokernel f.hom` to `kernel f.hom` in a periodic
degree, obtained by composing the connecting isomorphisms of the two canonical rows. -/
noncomputable def boundaryIso (f : Hom K L) (hK : K.toCochainComplex.Acyclic)
    (hL : L.toCochainComplex.Acyclic) (hker : KernelDifferentialsVanish f)
    (hcoker : CokernelDifferentialsVanish f) (i : ZMod 2) :
    cokernel f.hom ≅ kernel f.hom :=
  (cokernelHomologyIso f hcoker i).symm ≪≫
    (imageCokernelRow_shortExact f).δIso i
      ((ComplexShape.up (ZMod 2)).next i)
      (ComplexShape.HasOutgoing.rel_next (ComplexShape.up (ZMod 2)) i)
      ((HomologicalComplex.acyclic_iff_forall_isZero_homology L.toCochainComplex).mp hL i)
      ((HomologicalComplex.acyclic_iff_forall_isZero_homology L.toCochainComplex).mp hL
        ((ComplexShape.up (ZMod 2)).next i)) ≪≫
    (kernelImageRow_shortExact f).δIso ((ComplexShape.up (ZMod 2)).next i)
      ((ComplexShape.up (ZMod 2)).next ((ComplexShape.up (ZMod 2)).next i))
      (ComplexShape.HasOutgoing.rel_next (ComplexShape.up (ZMod 2))
        ((ComplexShape.up (ZMod 2)).next i))
      ((HomologicalComplex.acyclic_iff_forall_isZero_homology K.toCochainComplex).mp hK
        ((ComplexShape.up (ZMod 2)).next i))
      ((HomologicalComplex.acyclic_iff_forall_isZero_homology K.toCochainComplex).mp hK
        ((ComplexShape.up (ZMod 2)).next ((ComplexShape.up (ZMod 2)).next i))) ≪≫
    kernelHomologyIso f hker
      ((ComplexShape.up (ZMod 2)).next ((ComplexShape.up (ZMod 2)).next i))

/-- The morphism of `boundaryIso` is the transported composite of the two connecting maps. -/
theorem boundaryIso_hom (f : Hom K L) (hK : K.toCochainComplex.Acyclic)
    (hL : L.toCochainComplex.Acyclic) (hker : KernelDifferentialsVanish f)
    (hcoker : CokernelDifferentialsVanish f) (i : ZMod 2) :
    (boundaryIso f hK hL hker hcoker i).hom =
      ((cokernelHomologyIso f hcoker i).symm ≪≫
        (imageCokernelRow_shortExact f).δIso i
          ((ComplexShape.up (ZMod 2)).next i)
          (ComplexShape.HasOutgoing.rel_next (ComplexShape.up (ZMod 2)) i)
          ((HomologicalComplex.acyclic_iff_forall_isZero_homology L.toCochainComplex).mp hL i)
          ((HomologicalComplex.acyclic_iff_forall_isZero_homology L.toCochainComplex).mp hL
            ((ComplexShape.up (ZMod 2)).next i)) ≪≫
        (kernelImageRow_shortExact f).δIso ((ComplexShape.up (ZMod 2)).next i)
          ((ComplexShape.up (ZMod 2)).next ((ComplexShape.up (ZMod 2)).next i))
          (ComplexShape.HasOutgoing.rel_next (ComplexShape.up (ZMod 2))
            ((ComplexShape.up (ZMod 2)).next i))
          ((HomologicalComplex.acyclic_iff_forall_isZero_homology K.toCochainComplex).mp hK
            ((ComplexShape.up (ZMod 2)).next i))
          ((HomologicalComplex.acyclic_iff_forall_isZero_homology K.toCochainComplex).mp hK
            ((ComplexShape.up (ZMod 2)).next ((ComplexShape.up (ZMod 2)).next i))) ≪≫
        kernelHomologyIso f hker
          ((ComplexShape.up (ZMod 2)).next ((ComplexShape.up (ZMod 2)).next i))).hom := by
  rfl

/-- The boundary automorphism representing `α₀⁻¹ ∘ α₁`. -/
noncomputable def boundaryAutomorphism (f : Hom K L) (hK : K.toCochainComplex.Acyclic)
    (hL : L.toCochainComplex.Acyclic) (hker : KernelDifferentialsVanish f)
    (hcoker : CokernelDifferentialsVanish f) : cokernel f.hom ≅ cokernel f.hom :=
  boundaryIso f hK hL hker hcoker 1 ≪≫ (boundaryIso f hK hL hker hcoker 0).symm

/-- The boundary automorphism is `boundaryIso f 1 ≪≫ (boundaryIso f 0).symm`. -/
theorem boundaryAutomorphism_def (f : Hom K L) (hK : K.toCochainComplex.Acyclic)
    (hL : L.toCochainComplex.Acyclic) (hker : KernelDifferentialsVanish f)
    (hcoker : CokernelDifferentialsVanish f) :
    boundaryAutomorphism f hK hL hker hcoker =
      boundaryIso f hK hL hker hcoker 1 ≪≫ (boundaryIso f hK hL hker hcoker 0).symm := by
  rfl

end CategoryTheory.TwoPeriodicEndomorphism.Hom

namespace CategoryTheory.TwoPeriodicEndomorphism.Hom

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {K L : TwoPeriodicEndomorphism (ModuleCat.{v} R)}

/-- The kernel of a map out of a finite-length module has finite length. -/
theorem kernel_isFiniteLength (f : Hom K L) (hK : IsFiniteLength R K.X) :
    IsFiniteLength R (kernel f.hom : ModuleCat R) := by
  exact hK.of_injective (f := (kernel.ι f.hom).hom)
    ((ModuleCat.mono_iff_injective (kernel.ι f.hom)).mp inferInstance)

/-- The cokernel of a map into a finite-length module has finite length. -/
theorem cokernel_isFiniteLength (f : Hom K L) (hL : IsFiniteLength R L.X) :
    IsFiniteLength R (cokernel f.hom : ModuleCat R) := by
  exact hL.of_surjective (f := (cokernel.π f.hom).hom)
    ((ModuleCat.epi_iff_surjective (cokernel.π f.hom)).mp inferInstance)

end CategoryTheory.TwoPeriodicEndomorphism.Hom
