module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.RingTheory.RingHom.SquareZero
import Mathlib.Tactic.CrossRefAttribute

/-!
# Kernel of a square-zero ring homomorphism as a module over the target

The kernel of a square-zero surjection `f : R' →+* R` is canonically an `R`-module, since
`I^2 = ⊥` makes `I` an `(R' ⧸ I)`-module and `R' ⧸ I ≃+* R`.  Base change along `R' →+* S'`
produces the comparison `I ⊗[R] S ⟶ J` with `S = S' ⊗[R'] R` and `J = ker(S' → S)`.
-/

@[expose] public section

open TensorProduct

noncomputable section

universe u

namespace ModuleCat.SquareZeroExtension

variable {R' R : Type u} [CommRing R'] [CommRing R]

/-- The kernel of a square-zero extension is annihilated by itself. -/
theorem isTorsionBySet_ker (f : R' →+* R) [f.IsSquareZeroExtension] :
    Module.IsTorsionBySet R' (RingHom.ker f) (RingHom.ker f) := sorry

/-- The kernel of a square-zero extension is a module over `R' ⧸ ker f`. -/
noncomputable instance instModuleKerQuot (f : R' →+* R) [f.IsSquareZeroExtension] :
    Module (R' ⧸ RingHom.ker f) (RingHom.ker f) :=
  (isTorsionBySet_ker f).module

/-- The kernel of a square-zero extension `f : R' →+* R` is an `R`-module, by transporting
the quotient module structure along `R' ⧸ ker f ≃+* R`. -/
noncomputable instance instModuleKer (f : R' →+* R) [hf : f.IsSquareZeroExtension] :
    Module R (RingHom.ker f) :=
  Module.compHom (RingHom.ker f)
    (RingHom.quotientKerEquivOfSurjective hf.surjective).symm.toRingHom

/-- The kernel of a square-zero extension, as an object of `ModuleCat R`. -/
def kernelModule (f : R' →+* R) [f.IsSquareZeroExtension] : ModuleCat.{u} R :=
  ModuleCat.of R (RingHom.ker f)


/-- Scalar multiplication on `kernelModule f` is the transported `R`-action on `ker f`. -/
theorem smul_kernelModule (f : R' →+* R) [f.IsSquareZeroExtension]
    (r : R) (x : RingHom.ker f) :
    r • x =
      (RingHom.quotientKerEquivOfSurjective
          (RingHom.IsSquareZeroExtension.surjective (f := f))).symm r • x := sorry


variable {S' : Type u} [CommRing S']

/-- The base-changed target `S' ⊗[R'] R` of a square-zero extension along `R' →+* S'`. -/
abbrev tensorCodomain (f : R' →+* R) (g : R' →+* S') : Type u :=
  @TensorProduct R' _ S' R _ _ g.toAlgebra.toModule f.toAlgebra.toModule

/-- The commutative ring structure on `S' ⊗[R'] R`. -/
instance instCommRing_tensorCodomain (f : R' →+* R) (g : R' →+* S') :
    CommRing (tensorCodomain f g) :=
  @Algebra.TensorProduct.instCommRing R' S' R _ _ g.toAlgebra _ f.toAlgebra

/-- The canonical ring map `S' →+* S' ⊗[R'] R`. -/
def tensorCodomainRingHom (f : R' →+* R) (g : R' →+* S') :
    S' →+* tensorCodomain f g :=
  @Algebra.TensorProduct.includeLeftRingHom R' S' R _ _ g.toAlgebra _ f.toAlgebra

/-- The canonical ring map `R →+* S' ⊗[R'] R`. -/
def tensorCodomainIncludeRight (f : R' →+* R) (g : R' →+* S') :
    R →+* tensorCodomain f g :=
  @AlgHom.toRingHom R' R (tensorCodomain f g) _ _ _
    f.toAlgebra
    (@Algebra.TensorProduct.instAlgebra R' S' R _ _ g.toAlgebra _ f.toAlgebra)
    (@Algebra.TensorProduct.includeRight R' S' R _ _ g.toAlgebra _ f.toAlgebra)

/-- The `R`-algebra structure on `S' ⊗[R'] R` via the right tensor factor. -/
instance instAlgebra_tensorCodomain (f : R' →+* R) (g : R' →+* S') :
    Algebra R (tensorCodomain f g) :=
  (tensorCodomainIncludeRight f g).toAlgebra

/-- Base change of a square-zero extension along `R' →+* S'` remains square-zero. -/
instance instIsSquareZero_tensor (f : R' →+* R) [f.IsSquareZeroExtension]
    (g : R' →+* S') :
    (tensorCodomainRingHom f g).IsSquareZeroExtension := sorry

/-- Restriction of scalars of the base-changed kernel along `R → S`. -/
noncomputable instance instModuleKer_restrict (f : R' →+* R) [f.IsSquareZeroExtension]
    (g : R' →+* S') :
    Module R (RingHom.ker (tensorCodomainRingHom f g)) :=
  Module.compHom (RingHom.ker (tensorCodomainRingHom f g))
    (tensorCodomainIncludeRight f g)

/-- The `R`-action on the base-changed kernel is compatible with the `S`-action. -/
instance instIsScalarTower_ker (f : R' →+* R) [f.IsSquareZeroExtension]
    (g : R' →+* S') :
    IsScalarTower R (tensorCodomain f g)
      (RingHom.ker (tensorCodomainRingHom f g)) := sorry

/-- The image of `i : ker f` in `S'` lies in the kernel of `S' → S' ⊗[R'] R`. -/
theorem mem_ker_tensorCodomainRingHom (f : R' →+* R) [f.IsSquareZeroExtension]
    (g : R' →+* S') (i : RingHom.ker f) :
    tensorCodomainRingHom f g (g i.val) = 0 := sorry

/-- The canonical `R`-linear map sending `i : ker f` to its image in
`ker(S' → S' ⊗[R'] R)`. -/
def kernelToBaseChange (f : R' →+* R) [f.IsSquareZeroExtension] (g : R' →+* S') :
    RingHom.ker f →ₗ[R] RingHom.ker (tensorCodomainRingHom f g) where
  toFun i := ⟨g i.val, mem_ker_tensorCodomainRingHom f g i⟩
  map_add' i j := by
    apply Subtype.ext
    exact g.map_add i.val j.val
  map_smul' := sorry


/-- The comparison morphism `S ⊗[R] I ⟶ J` in `ModuleCat S`, where `S = S' ⊗[R'] R`
and `J = ker(S' → S)`. -/
def kernelBaseChange (f : R' →+* R) [f.IsSquareZeroExtension] (g : R' →+* S') :
    ModuleCat.of (tensorCodomain f g)
        (tensorCodomain f g ⊗[R] RingHom.ker f) ⟶
      kernelModule (tensorCodomainRingHom f g) :=
  ModuleCat.ofHom
    (LinearMap.liftBaseChange (tensorCodomain f g) (kernelToBaseChange f g))

/-- `kernelBaseChange` on elementary tensors is the `S`-action on the image of `i`. -/
theorem kernelBaseChange_tmul (f : R' →+* R) [f.IsSquareZeroExtension]
    (g : R' →+* S') (s : tensorCodomain f g) (i : RingHom.ker f) :
    (kernelBaseChange f g).hom (s ⊗ₜ[R] i) =
      s • kernelToBaseChange f g i := sorry

end ModuleCat.SquareZeroExtension
