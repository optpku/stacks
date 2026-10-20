module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.CategoryTheory.Fibered.InSetoids.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StructureSheaf.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.WithSection

/-!
# Isomorphism classes of section-rigidified invertible modules

Under universal preservation of the structure sheaf, rigidification removes
automorphisms, and the classes are the kernels of section pullback.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard.WithSection

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The family of kernels of section pullback, indexed by maps from a fixed test scheme. -/
abbrev KernelClasses (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) (T : Over S) :=
  Σ h : ofOver T ⟶ B, (sectionPicard f σ hσ (CostructuredArrow.mk h)).ker

/-- The Picard class of the actual invertible module stored in a Picard object. -/
private def picardClassOfObj {f : X ⟶ B} (x : Picard.Obj f) :
    (CohStack.fiber f x.σ).PicardGroup :=
  @MonoidalCategory.PicardGroup.mk (CohStack.fiber f x.σ).Modules _ _ x.line x.invertible

/-- A trivialization along the section makes the underlying Picard class lie in the kernel. -/
private theorem isoClassOfFiber_mem_ker {f : X ⟶ B} {σ : B ⟶ X}
    {hσ : σ ≫ f = 𝟙 B} {T : Over S} (x : (p f σ hσ).Fiber T) :
    sectionPicard f σ hσ x.1.toPicard.σ (picardClassOfObj x.1.toPicard) = 0 := sorry

/-- The kernel class of a rigidified object, transported to its fixed test scheme. -/
@[no_expose] def isoClassOfFiber {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B} {T : Over S}
    (x : (p f σ hσ).Fiber T) : KernelClasses f σ hσ T :=
  x.property ▸
    (⟨x.1.toPicard.σ.hom, ⟨picardClassOfObj x.1.toPicard,
      isoClassOfFiber_mem_ker x⟩⟩ : KernelClasses f σ hσ x.1.toPicard.σ.left)

/-- The index of the kernel class is the original base map transported to the fixed test scheme. -/
theorem isoClassOfFiber_hom {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {T : Over S} (x : (p f σ hσ).Fiber T) :
    (isoClassOfFiber x).1 =
      eqToHom (congrArg ofOver x.property.symm) ≫ x.1.toPicard.σ.hom := sorry

/-- Isomorphic rigidified fibre objects have the same kernel class. -/
theorem isoClassOfFiber_eq_of_isIsomorphic {f : X ⟶ B} {σ : B ⟶ X}
    {hσ : σ ≫ f = 𝟙 B} {T : Over S} {x y : (p f σ hσ).Fiber T}
    (h : IsIsomorphic x y) : isoClassOfFiber x = isoClassOfFiber y := sorry

/-- The pulled-back representative of a kernel class has zero Picard class. -/
theorem kernelRepresentative_class {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {T : Over S} (c : KernelClasses f σ hσ T) :
    Modules.picardClass
      ((Modules.pullback (sectionFiber f σ hσ (CostructuredArrow.mk c.1))).obj
        (PicardGroup.repr c.2.1)) = 0 := sorry

/-- A trivialization of the actual pulled-back Picard representative of a kernel element. -/
private def kernelTrivialization {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {T : Over S} (c : KernelClasses f σ hσ T) :
    𝟙_ (ofOver T).Modules ≅
      (Modules.pullback (sectionFiber f σ hσ (CostructuredArrow.mk c.1))).obj
        (PicardGroup.repr c.2.1) :=
  (Classical.choice
    ((MonoidalCategory.PicardGroup.mk_eq_zero_iff
      ((Modules.pullback (sectionFiber f σ hσ (CostructuredArrow.mk c.1))).obj
        (PicardGroup.repr c.2.1))).mp c.2.property)).symm

/-- A rigidified fibre object reconstructed from the representative of a kernel class. -/
@[no_expose] def fiberOfIsoClass {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B} {T : Over S}
    (c : KernelClasses f σ hσ T) : (p f σ hσ).Fiber T :=
  ⟨ofLine (CostructuredArrow.mk c.1) (PicardGroup.repr c.2.1)
    (kernelTrivialization c), rfl⟩

/-- Reconstruction uses the canonical test object and recovers the supplied Picard class. -/
theorem fiberOfIsoClass_spec {f : X ⟶ B} {σ : B ⟶ X} {hσ : σ ≫ f = 𝟙 B}
    {T : Over S} (c : KernelClasses f σ hσ T) :
    (fiberOfIsoClass c).1.toPicard.σ = CostructuredArrow.mk c.1 ∧
      isoClassOfFiber (fiberOfIsoClass c) = c := sorry

/-- Universal preservation of the structure sheaf makes the rigidified projection fibred in setoids. -/
instance instIsFiberedInSetoids (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    [IsIsoBaseChangeStructurePushforward f] :
    Functor.IsFibered.InSetoids (p f σ hσ) := sorry

/-- The class map forgetting the trivialization descends to isomorphism classes of fibre objects. -/
def isoClassMap (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) (T : Over S) :
    isomorphismClasses.obj (Cat.of ((p f σ hσ).Fiber T)) → KernelClasses f σ hσ T :=
  Quotient.lift isoClassOfFiber fun _ _ h ↦ isoClassOfFiber_eq_of_isIsomorphic h

/-- Reconstructing the kernel class of a fibre isomorphism class recovers that class. -/
theorem isoClassMap_leftInv (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    [IsIsoBaseChangeStructurePushforward f] (T : Over S) :
    Function.LeftInverse (fun c ↦ Quotient.mk _ (fiberOfIsoClass c))
      (isoClassMap f σ hσ T) := sorry

/-- Taking the kernel class of a reconstructed representative recovers the kernel element. -/
theorem isoClassMap_rightInv (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    [IsIsoBaseChangeStructurePushforward f] (T : Over S) :
    Function.RightInverse (fun c ↦ Quotient.mk _ (fiberOfIsoClass c))
      (isoClassMap f σ hσ T) := sorry

/-- Fibre isomorphism classes of rigidified invertible modules are the family of section kernels. -/
def isoClassEquiv (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    [IsIsoBaseChangeStructurePushforward f] (T : Over S) :
    isomorphismClasses.obj (Cat.of ((p f σ hσ).Fiber T)) ≃ KernelClasses f σ hσ T where
  toFun := isoClassMap f σ hσ T
  invFun c := Quotient.mk _ (fiberOfIsoClass c)
  left_inv := isoClassMap_leftInv f σ hσ T
  right_inv := isoClassMap_rightInv f σ hσ T

/-- The equivalence sends a fibre object's class to its actual kernel class. -/
theorem isoClassEquiv_apply (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    [IsIsoBaseChangeStructurePushforward f] {T : Over S}
    (x : (p f σ hσ).Fiber T) :
    isoClassEquiv f σ hσ T (Quotient.mk _ x) = isoClassOfFiber x := sorry

/-- The inverse equivalence is the class of the specified reconstructed representative. -/
theorem isoClassEquiv_symm_apply (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    [IsIsoBaseChangeStructurePushforward f] {T : Over S}
    (c : KernelClasses f σ hσ T) :
    (isoClassEquiv f σ hσ T).symm c = Quotient.mk _ (fiberOfIsoClass c) := sorry

end AlgebraicGeometry.AlgebraicSpace.Picard.WithSection
