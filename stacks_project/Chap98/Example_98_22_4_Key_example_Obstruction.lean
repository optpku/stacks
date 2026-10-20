/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Extension.Generators
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Ext.Functor
public import ReasLib.RingTheory.AlgHom.Lifting
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.BaseChange
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Canonical
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Concentration
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Derived
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.ExtendScalars
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.RestrictScalars.Map
public import ReasLib.RingTheory.RingHom.LiftingSquare
public import ReasLib.RingTheory.RingHom.SquareZero
public import stacks_project.Chap98.Definition_98_22_1_DeformationSituation

/-!
# Obstruction modules for presented algebras

The Ext¹(NL, I)-valued obstruction to lifting a presented Λ-algebra through a
square-zero extension, together with the Hom-coker model and the evaluation-of-lifts
formula.
-/

@[expose] public section

open CategoryTheory
open Algebra
open Algebra.Generators
open Algebra.Extension
open MvPolynomial
open scoped NaiveCotangent

noncomputable section

universe u

namespace Algebra.NaiveCotangent.Obstruction

public section

/-- The naive presentation of `MvPolynomial ι Λ ⧸ J` with generators the images of the
indeterminates. -/
public abbrev presentation {Λ ι : Type u} [CommRing Λ] (J : Ideal (MvPolynomial ι Λ)) :
    Generators Λ (MvPolynomial ι Λ ⧸ J) ι :=
  Generators.naive

/-- The designated generators of `presentation` are the classes of the indeterminates. -/
theorem presentation_val {Λ ι : Type u} [CommRing Λ] (J : Ideal (MvPolynomial ι Λ)) (i : ι) :
    (presentation J).val i = Ideal.Quotient.mk J (X i) :=
  sorry

/-- The kernel of `presentation` is the original ideal `J`. -/
theorem presentation_ker {Λ ι : Type u} [CommRing Λ] (J : Ideal (MvPolynomial ι Λ)) :
    (presentation J).ker = J :=
  sorry

/-- Canonical homotopy equivalence from `NL{R⁄Λ}` to the two-term presentation complex. -/
public def homotopyEquiv {Λ ι : Type u} [CommRing Λ] (J : Ideal (MvPolynomial ι Λ)) :
    HomotopyEquiv
      (NL{(MvPolynomial ι Λ ⧸ J) ⁄ Λ})
      (NaiveCotangent.complex (presentation J).toExtension) :=
  NaiveCotangent.generatorsHomotopyEquiv
    (Generators.self Λ (MvPolynomial ι Λ ⧸ J)) (presentation J)

/-- `homotopyEquiv` is the canonical comparison of self and naive presentations. -/
theorem homotopyEquiv_eq {Λ ι : Type u} [CommRing Λ] (J : Ideal (MvPolynomial ι Λ)) :
    homotopyEquiv J =
      NaiveCotangent.generatorsHomotopyEquiv
        (Generators.self Λ (MvPolynomial ι Λ ⧸ J)) (presentation J) :=
  sorry

/-- The degree-one term of the presentation complex identifies with `J/J²`. -/
def presentation_liftEquiv {Λ ι : Type u} [CommRing Λ] (J : Ideal (MvPolynomial ι Λ)) :
    NaiveCotangent.Lift (presentation J).toExtension ≃ₗ[MvPolynomial ι Λ ⧸ J]
      (presentation J).toExtension.Cotangent :=
  NaiveCotangent.liftEquiv (presentation J).toExtension

/-- `presentation_liftEquiv` is the universe-lift identification of the conormal module. -/
theorem presentation_liftEquiv_eq {Λ ι : Type u} [CommRing Λ] (J : Ideal (MvPolynomial ι Λ)) :
    presentation_liftEquiv J = NaiveCotangent.liftEquiv (presentation J).toExtension :=
  sorry

/-- The degree-zero term of the presentation complex is free on the classes `d x_i`. -/
def presentation_cotangentSpaceBasis {Λ ι : Type u} [CommRing Λ]
    (J : Ideal (MvPolynomial ι Λ)) :
    Module.Basis ι (MvPolynomial ι Λ ⧸ J) (presentation J).toExtension.CotangentSpace :=
  (presentation J).cotangentSpaceBasis

/-- `presentation_cotangentSpaceBasis` is the canonical cotangent-space basis. -/
theorem presentation_cotangentSpaceBasis_eq {Λ ι : Type u} [CommRing Λ]
    (J : Ideal (MvPolynomial ι Λ)) :
    presentation_cotangentSpaceBasis J = (presentation J).cotangentSpaceBasis :=
  sorry

/-- The kernel of a square-zero algebra map `π : A' → A`. -/
public abbrev kernelModule {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] : Type u :=
  RingHom.ker π.toRingHom

/-- `kernelModule π` is the kernel of `π`. -/
theorem kernelModule_eq {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] :
    kernelModule π = RingHom.ker π.toRingHom :=
  sorry

/-- Homomorphisms from `J/J²` into an `A`-module, linear over the presented ring along `φ`. -/
abbrev relationHom {Λ ι A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (N : Type u) [AddCommGroup N] [Module A N] : Type u :=
  (presentation J).toExtension.Cotangent →ₛₗ[φ.toRingHom] N

/-- Homomorphisms from the free module on the presentation generators into an `A`-module. -/
abbrev generatorHom {Λ ι A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (N : Type u) [AddCommGroup N] [Module A N] : Type u :=
  ((ι →₀ MvPolynomial ι Λ ⧸ J) →ₛₗ[φ.toRingHom] N)

/-- Precomposition with the cotangent differential. -/
def homDifferential {Λ ι A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (N : Type u) [AddCommGroup N] [Module A N] :
    ((presentation J).toExtension.CotangentSpace →ₛₗ[φ.toRingHom] N) →ₗ[A]
      relationHom J φ N where
  toFun g := g.comp (presentation J).toExtension.cotangentComplex
  map_add' := sorry
  map_smul' := sorry

/-- Precomposition with `J/J² ⟶ ⊕ R d x_i` on Hom-spaces. -/
def generatorToRelation {Λ ι A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (N : Type u) [AddCommGroup N] [Module A N] :
    generatorHom J φ N →ₗ[A] relationHom J φ N where
  toFun g :=
    g.comp
      ((presentation J).cotangentSpaceBasis.repr.toLinearMap ∘ₗ
        (presentation J).toExtension.cotangentComplex)
  map_add' := sorry
  map_smul' := sorry

/-- The Hom-coker value of a coefficient module along `φ`. -/
def functorObj {Λ ι A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (N : ModuleCat A) : ModuleCat A :=
  ModuleCat.of A (relationHom J φ N ⧸ LinearMap.range (homDifferential J φ N))

/-- Postcomposition on Hom-coker values. -/
def functorMap {Λ ι A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    {N N' : ModuleCat A} (f : N ⟶ N') :
    functorObj J φ N ⟶ functorObj J φ N' :=
  ModuleCat.ofHom
    { toFun := fun x ↦
        Submodule.Quotient.mk
          { toFun := fun y ↦ f.hom
              ((Function.surjInv (Submodule.mkQ_surjective
                (LinearMap.range (homDifferential J φ N))) x) y)
            map_add' := sorry
            map_smul' := sorry }
      map_add' := sorry
      map_smul' := sorry }

/-- The Hom-coker functor `N ↦ Hom_R(J/J², N) / Hom_R(R^{⊕ι}, N)` along `φ`. -/
def functor {Λ ι A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    ModuleCat A ⥤ ModuleCat A where
  obj := functorObj J φ
  map := functorMap J φ
  map_id := sorry
  map_comp := sorry

/-- The value of `functor` on a coefficient module. -/
theorem functor_obj {Λ ι A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (N : ModuleCat A) :
    (functor J φ).obj N = functorObj J φ N :=
  sorry

/-- The induced map of `functor` on morphisms of coefficient modules. -/
theorem functor_map {Λ ι A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    {N N' : ModuleCat A} (f : N ⟶ N') :
    (functor J φ).map f = functorMap J φ f :=
  sorry

/-- The obstruction module `O_x(I)` as the Hom-coker of the presentation complex. -/
public abbrev module {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) : Type u :=
  relationHom J φ (kernelModule π) ⧸ LinearMap.range (homDifferential J φ (kernelModule π))

/-- The obstruction module is the value of `functor` on the square-zero kernel. -/
theorem module_def {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    module π J φ =
      (relationHom J φ (kernelModule π) ⧸
        LinearMap.range (homDifferential J φ (kernelModule π))) :=
  sorry

/-- The source Hom-coker `Hom_R(J/J², I) / Hom_R(R^{⊕ι}, I)`. -/
abbrev homCoker {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) : Type u :=
  relationHom J φ (kernelModule π) ⧸ LinearMap.range (generatorToRelation J φ (kernelModule π))

/-- The comparison from the cotangent Hom-coker to the free-generator Hom-coker. -/
def homCokerMap {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    module π J φ →ₗ[A] homCoker π J φ :=
  (LinearMap.range (homDifferential J φ (kernelModule π))).liftQ
    (LinearMap.range (generatorToRelation J φ (kernelModule π))).mkQ sorry

/-- Identification of the obstruction module with `Hom_R(J/J², I) / Hom_R(R^{⊕ι}, I)`. -/
public def homCokerEquiv {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    module π J φ ≃ₗ[A] homCoker π J φ :=
  LinearEquiv.ofBijective (homCokerMap π J φ) sorry

/-- `homCokerEquiv` applies the cotangent-space basis comparison. -/
theorem homCokerEquiv_apply {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (x : module π J φ) :
    homCokerEquiv π J φ x = homCokerMap π J φ x :=
  sorry

/-- The Ext functor `N ↦ Ext¹_R(NL{R⁄Λ}, N)`. -/
def extFunctor {Λ ι : Type u} [CommRing Λ] (J : Ideal (MvPolynomial ι Λ)) :
    ModuleCat (MvPolynomial ι Λ ⧸ J) ⥤ ModuleCat (MvPolynomial ι Λ ⧸ J) :=
  DerivedCategory.Ext.moduleFunctor
    (Algebra.naiveCotangentObject Λ (MvPolynomial ι Λ ⧸ J)) (1 : ℤ)

/-- The value of `extFunctor` on a coefficient module. -/
theorem extFunctor_obj {Λ ι : Type u} [CommRing Λ] (J : Ideal (MvPolynomial ι Λ))
    (N : ModuleCat (MvPolynomial ι Λ ⧸ J)) :
    (extFunctor J).obj N =
      (DerivedCategory.Ext.moduleFunctor
        (Algebra.naiveCotangentObject Λ (MvPolynomial ι Λ ⧸ J)) (1 : ℤ)).obj N :=
  sorry

/-- The coefficient module `I` viewed as an `R`-module along `φ`. -/
def kernelAsPresentedModule {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    ModuleCat (MvPolynomial ι Λ ⧸ J) :=
  -- Local instance justification (noncanonical choice): I is an R-module along φ.
  letI : Module (MvPolynomial ι Λ ⧸ J) (kernelModule π) :=
    Module.compHom (kernelModule π) φ.toRingHom
  ModuleCat.of (MvPolynomial ι Λ ⧸ J) (kernelModule π)

/-- `kernelAsPresentedModule` is `I` with the restricted `R`-action. -/
theorem kernelAsPresentedModule_eq {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    kernelAsPresentedModule π J φ =
      -- Local instance justification (noncanonical choice): I is an R-module along φ.
      letI : Module (MvPolynomial ι Λ ⧸ J) (kernelModule π) :=
        Module.compHom (kernelModule π) φ.toRingHom
      ModuleCat.of (MvPolynomial ι Λ ⧸ J) (kernelModule π) :=
  sorry

/-- A chosen relation-hom representative of a Hom-coker class. -/
def moduleRepr {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (x : module π J φ) : relationHom J φ (kernelModule π) :=
  Function.surjInv
    (Submodule.mkQ_surjective
      (LinearMap.range (homDifferential J φ (kernelModule π)))) x

/-- `moduleRepr` is a section of the Hom-coker quotient map. -/
theorem moduleRepr_mk {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (x : module π J φ) :
    Submodule.Quotient.mk (moduleRepr π J φ x) = x :=
  sorry

/-- The degree-one map of the presentation complex associated to a relation homomorphism. -/
def presentationDegreeOne {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (f : relationHom J φ (kernelModule π)) :
    (NaiveCotangent.complex (presentation J).toExtension).X 1 ⟶
      kernelAsPresentedModule π J φ :=
  -- Local instance justification (noncanonical choice): I is an R-module along φ.
  letI : Module (MvPolynomial ι Λ ⧸ J) (kernelModule π) :=
    Module.compHom (kernelModule π) φ.toRingHom
  ModuleCat.ofHom
    { toFun := fun y ↦ f (presentation_liftEquiv J y)
      map_add' := sorry
      map_smul' := sorry }

/-- `presentationDegreeOne` evaluates the relation map on the lifted conormal. -/
theorem presentationDegreeOne_apply {Λ ι A' A : Type u}
    [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (f : relationHom J φ (kernelModule π))
    (y : NaiveCotangent.Lift (presentation J).toExtension) :
    presentationDegreeOne π J φ f y = f (presentation_liftEquiv J y) :=
  sorry

/-- Differentials into degree one vanish after the presentation degree-one map. -/
theorem presentationToSingle_d_comp {Λ ι A' A : Type u}
    [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (f : (NaiveCotangent.complex (presentation J).toExtension).X 1 ⟶
      kernelAsPresentedModule π J φ)
    (i : ℕ) (hi : (ComplexShape.down ℕ).Rel i 1) :
    (NaiveCotangent.complex (presentation J).toExtension).d i 1 ≫ f = 0 :=
  sorry

/-- Chain map from the presentation complex to `I[1]`, zero in degree 0. -/
def presentationToSingle {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (f : relationHom J φ (kernelModule π)) :
    NaiveCotangent.complex (presentation J).toExtension ⟶
      (HomologicalComplex.single
        (ModuleCat (MvPolynomial ι Λ ⧸ J)) (ComplexShape.down ℕ) 1).obj
        (kernelAsPresentedModule π J φ) :=
  HomologicalComplex.mkHomToSingle (presentationDegreeOne π J φ f)
    (presentationToSingle_d_comp π J φ (presentationDegreeOne π J φ f))

/-- `presentationToSingle` is the degree-one chain map associated to a relation homomorphism. -/
theorem presentationToSingle_eq {Λ ι A' A : Type u}
    [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (f : relationHom J φ (kernelModule π)) :
    presentationToSingle π J φ f =
      HomologicalComplex.mkHomToSingle (presentationDegreeOne π J φ f)
        (presentationToSingle_d_comp π J φ (presentationDegreeOne π J φ f)) :=
  sorry

/-- Derived morphism associated to a chain map into a degree-one single complex. -/
def derivedFromSingle {R : Type u} [CommRing R]
    {K : ChainComplex (ModuleCat R) ℕ} {N : ModuleCat R}
    (toSingle : K ⟶
      (HomologicalComplex.single (ModuleCat R) (ComplexShape.down ℕ) 1).obj N) :
    DerivedCategory.Q.obj (K.extend ComplexShape.embeddingDownNat) ⟶
      ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)⟦(1 : ℤ)⟧ :=
  DerivedCategory.Q.map (HomologicalComplex.extendMap toSingle
      ComplexShape.embeddingDownNat) ≫
    DerivedCategory.Q.map
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
        N 1 (-1 : ℤ) rfl).hom ≫
    ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso (1 : ℤ) (-1) 0
      (add_neg_cancel (1 : ℤ))).inv.app N

/-- `derivedFromSingle` is the derived image of a degree-one chain map. -/
theorem derivedFromSingle_eq {R : Type u} [CommRing R]
    {K : ChainComplex (ModuleCat R) ℕ} {N : ModuleCat R}
    (toSingle : K ⟶
      (HomologicalComplex.single (ModuleCat R) (ComplexShape.down ℕ) 1).obj N) :
    derivedFromSingle toSingle =
      DerivedCategory.Q.map (HomologicalComplex.extendMap toSingle
          ComplexShape.embeddingDownNat) ≫
        DerivedCategory.Q.map
          (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
            N 1 (-1 : ℤ) rfl).hom ≫
        ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso (1 : ℤ) (-1) 0
          (add_neg_cancel (1 : ℤ))).inv.app N :=
  sorry

/-- Linear comparison from the Hom-coker to `Ext¹_R(NL{R⁄Λ}, I)`. -/
def extMap {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    ((ModuleCat.restrictScalars φ.toRingHom).obj
        (ModuleCat.of A (module π J φ))) →ₗ[MvPolynomial ι Λ ⧸ J]
      (extFunctor J).obj (kernelAsPresentedModule π J φ) where
  toFun := fun x ↦
    derivedFromSingle
      ((homotopyEquiv J).hom ≫ presentationToSingle π J φ (moduleRepr π J φ x))
  map_add' := sorry
  map_smul' := sorry

/-- `extMap` sends a Hom-coker class to the derived morphism of its presentation chain map. -/
theorem extMap_apply {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (x : module π J φ) :
    extMap π J φ x =
      derivedFromSingle
        ((homotopyEquiv J).hom ≫ presentationToSingle π J φ (moduleRepr π J φ x)) :=
  sorry

/-- Identification of the obstruction module with `Ext¹_R(NL{R⁄Λ}, I)`. -/
public def extEquiv {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    ((ModuleCat.restrictScalars φ.toRingHom).obj
        (ModuleCat.of A (module π J φ))) ≃ₗ[MvPolynomial ι Λ ⧸ J]
      (extFunctor J).obj (kernelAsPresentedModule π J φ) :=
  LinearEquiv.ofBijective (extMap π J φ) sorry

/-- The two-term tensor model of `NL{R⁄Λ} ⊗_R A` along `φ`. -/
def tensorModel {Λ ι A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    ChainComplex (ModuleCat A) ℕ :=
  -- Local instance justification (noncanonical choice): the A-algebra structure on the presented ring is the chosen deformation map φ.
  letI : Algebra (MvPolynomial ι Λ ⧸ J) A := φ.toRingHom.toAlgebra
  -- Local instance justification (noncanonical choice): the tower Λ → R → A is induced by φ.
  letI : IsScalarTower Λ (MvPolynomial ι Λ ⧸ J) A :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  NaiveCotangent.BaseChange.tensorModel (presentation J).toExtension

/-- `tensorModel` is the base-change tensor model of the naive presentation. -/
theorem tensorModel_eq {Λ ι A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    tensorModel J φ =
      -- Local instance justification (noncanonical choice): the A-algebra structure on the presented ring is the chosen deformation map φ.
      letI : Algebra (MvPolynomial ι Λ ⧸ J) A := φ.toRingHom.toAlgebra
      -- Local instance justification (noncanonical choice): the tower Λ → R → A is induced by φ.
      letI : IsScalarTower Λ (MvPolynomial ι Λ ⧸ J) A :=
        IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
      NaiveCotangent.BaseChange.tensorModel (presentation J).toExtension :=
  sorry

/-- The degree-one map of the tensor model associated to a relation homomorphism. -/
def tensorDegreeOne {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (f : relationHom J φ (kernelModule π)) :
    (tensorModel J φ).X 1 ⟶ ModuleCat.of A (kernelModule π) :=
  -- Local instance justification (noncanonical choice): the A-algebra structure on the presented ring is the chosen deformation map φ.
  letI : Algebra (MvPolynomial ι Λ ⧸ J) A := φ.toRingHom.toAlgebra
  -- Local instance justification (noncanonical choice): the tower Λ → R → A is induced by φ.
  letI : IsScalarTower Λ (MvPolynomial ι Λ ⧸ J) A :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  -- Local instance justification (noncanonical choice): I is an R-module along φ.
  letI : Module (MvPolynomial ι Λ ⧸ J) (kernelModule π) :=
    Module.compHom (kernelModule π) φ.toRingHom
  -- Local instance justification (noncanonical choice): the R-action on I via φ is compatible with the A-action.
  letI : IsScalarTower (MvPolynomial ι Λ ⧸ J) A (kernelModule π) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  ModuleCat.ofHom
    (LinearMap.liftBaseChange A
      { toFun := f.toFun
        map_add' := sorry
        map_smul' := sorry })

/-- `tensorDegreeOne` is additive on the degree-one tensor component. -/
theorem tensorDegreeOne_add {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (f : relationHom J φ (kernelModule π))
    (x y : (tensorModel J φ).X 1) :
    tensorDegreeOne π J φ f (x + y) =
      tensorDegreeOne π J φ f x + tensorDegreeOne π J φ f y :=
  sorry

/-- Differentials into degree one vanish after the tensor-model degree-one map. -/
theorem tensorToSingle_d_comp {Λ ι A' A : Type u}
    [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (f : (tensorModel J φ).X 1 ⟶ ModuleCat.of A (kernelModule π))
    (i : ℕ) (hi : (ComplexShape.down ℕ).Rel i 1) :
    (tensorModel J φ).d i 1 ≫ f = 0 :=
  sorry

/-- Chain map from the tensor model to `I[1]`, zero in degree 0. -/
def tensorToSingle {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (f : relationHom J φ (kernelModule π)) :
    tensorModel J φ ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.down ℕ) 1).obj
        (ModuleCat.of A (kernelModule π)) :=
  HomologicalComplex.mkHomToSingle (tensorDegreeOne π J φ f)
    (tensorToSingle_d_comp π J φ (tensorDegreeOne π J φ f))

/-- `tensorToSingle` is the degree-one chain map of a relation homomorphism. -/
theorem tensorToSingle_eq {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (f : relationHom J φ (kernelModule π)) :
    tensorToSingle π J φ f =
      HomologicalComplex.mkHomToSingle (tensorDegreeOne π J φ f)
        (tensorToSingle_d_comp π J φ (tensorDegreeOne π J φ f)) :=
  sorry

/-- Linear comparison from the Hom-coker to `Ext¹_A(NL{R⁄Λ} ⊗_R A, I)`. -/
def baseChangeExtMap {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    module π J φ →ₗ[A]
      (DerivedCategory.Ext.moduleFunctor
        (DerivedCategory.Q.obj ((tensorModel J φ).extend ComplexShape.embeddingDownNat))
        (1 : ℤ)).obj (ModuleCat.of A (kernelModule π)) where
  toFun := fun x ↦
    derivedFromSingle (tensorToSingle π J φ (moduleRepr π J φ x))
  map_add' := sorry
  map_smul' := sorry

/-- `baseChangeExtMap` sends a Hom-coker class to the derived morphism of its tensor chain map. -/
theorem baseChangeExtMap_apply {Λ ι A' A : Type u}
    [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (x : module π J φ) :
    baseChangeExtMap π J φ x =
      derivedFromSingle (tensorToSingle π J φ (moduleRepr π J φ x)) :=
  sorry

/-- Identification of the obstruction module with `Ext¹_A(NL{R⁄Λ} ⊗_R A, I)`. -/
public def baseChangeExtEquiv {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    module π J φ ≃ₗ[A]
      (DerivedCategory.Ext.moduleFunctor
        (DerivedCategory.Q.obj ((tensorModel J φ).extend ComplexShape.embeddingDownNat))
        (1 : ℤ)).obj (ModuleCat.of A (kernelModule π)) :=
  LinearEquiv.ofBijective (baseChangeExtMap π J φ) sorry

/-- The three source identifications of the obstruction module. -/
theorem module_spec {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    Function.Bijective (homCokerEquiv π J φ).toLinearMap ∧
      Function.Bijective (extEquiv π J φ).toLinearMap ∧
      Function.Bijective (baseChangeExtEquiv π J φ).toLinearMap :=
  sorry

/-- The relation map sending the class of `f ∈ J` to `aeval a' f ∈ I`. -/
def relationMap {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (a' : ι → A') (ha' : ∀ i, π (a' i) = φ ((presentation J).val i)) :
    relationHom J φ (kernelModule π) where
  toFun x :=
    ⟨aeval a' (Function.surjInv Cotangent.mk_surjective x).1, sorry⟩
  map_add' := sorry
  map_smul' := sorry

/-- `relationMap` evaluates a cotangent representative by the chosen lifts. -/
theorem relationMap_apply {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (a' : ι → A') (ha' : ∀ i, π (a' i) = φ ((presentation J).val i))
    (f : (presentation J).ker) :
    relationMap π J φ a' ha' (Cotangent.mk f) = ⟨aeval a' f.1, sorry⟩ :=
  sorry

/-- The obstruction class of a choice of coordinate lifts. -/
public def ofLifts {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (a' : ι → A') (ha' : ∀ i, π (a' i) = φ ((presentation J).val i)) :
    module π J φ :=
  Submodule.Quotient.mk (relationMap π J φ a' ha')

/-- `ofLifts` is the class of `relationMap`. -/
theorem ofLifts_apply {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (a' : ι → A') (ha' : ∀ i, π (a' i) = φ ((presentation J).val i)) :
    ofLifts π J φ a' ha' = Submodule.Quotient.mk (relationMap π J φ a' ha') :=
  sorry

/-- Coordinatewise lifts of the images of the presentation generators. -/
def coordinateLift {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [hπ : π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    ι → A' :=
  fun i ↦ Function.surjInv hπ.surjective (φ ((presentation J).val i))

/-- `coordinateLift` lifts the images of the presentation generators. -/
theorem coordinateLift_spec {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) (i : ι) :
    π (coordinateLift π J φ i) = φ ((presentation J).val i) :=
  sorry

/-- The obstruction class `o_x(A')`. -/
public def obstruction {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    module π J φ :=
  ofLifts π J φ (coordinateLift π J φ) (coordinateLift_spec π J φ)

/-- The obstruction class agrees with the evaluation of any choice of coordinate lifts. -/
theorem obstruction_eq_ofLifts {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (a' : ι → A') (ha' : ∀ i, π (a' i) = φ ((presentation J).val i)) :
    obstruction π J φ = ofLifts π J φ a' ha' :=
  sorry

/-- The evaluation-of-lifts class is independent of the chosen lifts of the coordinates. -/
theorem independent {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (a₁ a₂ : ι → A')
    (ha₁ : ∀ i, π (a₁ i) = φ ((presentation J).val i))
    (ha₂ : ∀ i, π (a₂ i) = φ ((presentation J).val i)) :
    ofLifts π J φ a₁ ha₁ = ofLifts π J φ a₂ ha₂ :=
  sorry

/-- The obstruction vanishes if and only if `φ` lifts through `π`. -/
theorem eq_zero_iff_hasLift {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    obstruction π J φ = 0 ↔ AlgHom.HasLift π φ :=
  sorry

/-- The vanishing criterion is equivalently a lift of the associated ring-hom square. -/
theorem eq_zero_iff_toLiftingSquare {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    obstruction π J φ = 0 ↔ (AlgHom.toLiftingSquare π φ).HasLift :=
  sorry

/-- Postcomposition on square-zero kernels along a morphism of deformation squares. -/
def kernelMap {Λ A' A B' B : Type u}
    [CommRing Λ] [CommRing A'] [CommRing A] [CommRing B'] [CommRing B]
    [Algebra Λ A'] [Algebra Λ A] [Algebra Λ B'] [Algebra Λ B]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (ρ : B' →ₐ[Λ] B) [ρ.toRingHom.IsSquareZeroExtension]
    (τ : A' →ₐ[Λ] B') (σ : A →ₐ[Λ] B)
    (hcomm : ρ.comp τ = σ.comp π) :
    kernelModule π →ₗ[Λ] kernelModule ρ where
  toFun x := ⟨τ x.val, sorry⟩
  map_add' := sorry
  map_smul' := sorry

/-- `kernelMap` is evaluation of the source-ring map on kernel elements. -/
theorem kernelMap_apply {Λ A' A B' B : Type u}
    [CommRing Λ] [CommRing A'] [CommRing A] [CommRing B'] [CommRing B]
    [Algebra Λ A'] [Algebra Λ A] [Algebra Λ B'] [Algebra Λ B]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (ρ : B' →ₐ[Λ] B) [ρ.toRingHom.IsSquareZeroExtension]
    (τ : A' →ₐ[Λ] B') (σ : A →ₐ[Λ] B)
    (hcomm : ρ.comp τ = σ.comp π) (x : kernelModule π) :
    kernelMap π ρ τ σ hcomm x = ⟨τ x.val, sorry⟩ :=
  sorry

/-- The induced map of obstruction modules along a morphism of square-zero squares. -/
public def map {Λ ι A' A B' B : Type u}
    [CommRing Λ] [CommRing A'] [CommRing A] [CommRing B'] [CommRing B]
    [Algebra Λ A'] [Algebra Λ A] [Algebra Λ B'] [Algebra Λ B]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (ρ : B' →ₐ[Λ] B) [ρ.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ))
    (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) (ψ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] B)
    (τ : A' →ₐ[Λ] B') (σ : A →ₐ[Λ] B)
    (hcomm : ρ.comp τ = σ.comp π) (hφψ : ψ = σ.comp φ) :
    module π J φ →ₗ[A]
      (ModuleCat.restrictScalars σ.toRingHom).obj
        (ModuleCat.of B (module ρ J ψ)) where
  toFun := fun x ↦
    Submodule.Quotient.mk
      { toFun := fun c ↦
          kernelMap π ρ τ σ hcomm (moduleRepr π J φ x c)
        map_add' := sorry
        map_smul' := sorry }
  map_add' := sorry
  map_smul' := sorry

/-- Functoriality of the obstruction class along a morphism of square-zero squares. -/
theorem map_obstruction {Λ ι A' A B' B : Type u}
    [CommRing Λ] [CommRing A'] [CommRing A] [CommRing B'] [CommRing B]
    [Algebra Λ A'] [Algebra Λ A] [Algebra Λ B'] [Algebra Λ B]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (ρ : B' →ₐ[Λ] B) [ρ.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ))
    (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) (ψ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] B)
    (τ : A' →ₐ[Λ] B') (σ : A →ₐ[Λ] B)
    (hcomm : ρ.comp τ = σ.comp π) (hφψ : ψ = σ.comp φ) :
    map π ρ J φ ψ τ σ hcomm hφψ (obstruction π J φ) = obstruction ρ J ψ :=
  sorry

/-- The `A'`-algebra structure on `A` induced by a square-zero map `π`. -/
abbrev squareZeroAlgebra {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A) : Algebra A' A :=
  π.toRingHom.toAlgebra

/-- `squareZeroAlgebra` is the algebra structure of `π`. -/
theorem squareZeroAlgebra_eq {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A) :
    squareZeroAlgebra π = π.toRingHom.toAlgebra :=
  sorry

/-- The structure map of `squareZeroAlgebra π` is surjective. -/
theorem squareZero_algebraMap_surjective {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] :
    Function.Surjective (@algebraMap A' A _ _ (squareZeroAlgebra π)) :=
  sorry

/-- The empty-generator presentation of a square-zero surjection. -/
def squareZeroPresentation {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] :
    @Generators A' A PEmpty.{u + 1} _ _ (squareZeroAlgebra π) :=
  @Generators.ofSurjectiveAlgebraMap A' A _ _ (squareZeroAlgebra π)
    (squareZero_algebraMap_surjective π)

/-- `squareZeroPresentation` is the empty-generator presentation of `π`. -/
theorem squareZeroPresentation_eq {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] :
    squareZeroPresentation π =
      @Generators.ofSurjectiveAlgebraMap A' A _ _ (squareZeroAlgebra π)
        (squareZero_algebraMap_surjective π) :=
  sorry

/-- The two-term naive cotangent complex of the empty presentation of `π`. -/
abbrev squareZeroComplex {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] :
    ChainComplex (ModuleCat A) ℕ :=
  -- Local instance justification (noncanonical choice): the A'-algebra structure on A is π.
  letI : Algebra A' A := squareZeroAlgebra π
  Extension.NaiveCotangent.complex (squareZeroPresentation π).toExtension

/-- `squareZeroComplex` is the presentation complex of `squareZeroPresentation`. -/
theorem squareZeroComplex_eq {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] :
    squareZeroComplex π =
      -- Local instance justification (noncanonical choice): the A'-algebra structure on A is π.
      letI : Algebra A' A := squareZeroAlgebra π
      Extension.NaiveCotangent.complex (squareZeroPresentation π).toExtension :=
  sorry

/-- The lifted conormal module of the empty presentation of `π`. -/
abbrev squareZeroLift {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] : Type u :=
  -- Local instance justification (noncanonical choice): the A'-algebra structure on A is π.
  letI : Algebra A' A := squareZeroAlgebra π
  Extension.NaiveCotangent.Lift (squareZeroPresentation π).toExtension

/-- `squareZeroLift` is the degree-one term of `squareZeroComplex`. -/
theorem squareZeroLift_eq {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] :
    squareZeroLift π =
      -- Local instance justification (noncanonical choice): the A'-algebra structure on A is π.
      letI : Algebra A' A := squareZeroAlgebra π
      Extension.NaiveCotangent.Lift (squareZeroPresentation π).toExtension :=
  sorry

/-- The cotangent space of a square-zero empty presentation is a subsingleton. -/
theorem squareZero_cotangentSpace_subsingleton {Λ A' A : Type u}
    [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] :
    -- Local instance justification (noncanonical choice): the A'-algebra structure on A is π.
    letI : Algebra A' A := squareZeroAlgebra π
    Subsingleton (squareZeroPresentation π).toExtension.CotangentSpace :=
  sorry

/-- Canonical homotopy equivalence from `NL{A⁄A'}` to the empty-generator presentation complex. -/
def homotopyEquiv_squareZero {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] :
    HomotopyEquiv (RingHom.naiveCotangent π.toRingHom) (squareZeroComplex π) :=
  -- Local instance justification (noncanonical choice): the A'-algebra structure on A is π.
  letI : Algebra A' A := squareZeroAlgebra π
  Extension.NaiveCotangent.generatorsHomotopyEquiv
    (Generators.self A' A) (squareZeroPresentation π)

/-- `homotopyEquiv_squareZero` compares the self-presentation with the empty presentation. -/
theorem homotopyEquiv_squareZero_eq {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] :
    homotopyEquiv_squareZero π =
      -- Local instance justification (noncanonical choice): the A'-algebra structure on A is π.
      letI : Algebra A' A := squareZeroAlgebra π
      Extension.NaiveCotangent.generatorsHomotopyEquiv
        (Generators.self A' A) (squareZeroPresentation π) :=
  sorry

/-- Concentration of the empty-generator presentation onto the lifted kernel in degree one. -/
def homotopyEquiv_singleOne {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] :
    HomotopyEquiv
      (squareZeroComplex π)
      ((HomologicalComplex.single (ModuleCat A) (ComplexShape.down ℕ) 1).obj
        (ModuleCat.of A (squareZeroLift π))) :=
  -- Local instance justification (noncanonical choice): the A'-algebra structure on A is π.
  letI : Algebra A' A := squareZeroAlgebra π
  Extension.NaiveCotangent.homotopyEquivSingleOneOfSubsingleton
    (squareZeroPresentation π).toExtension (squareZero_cotangentSpace_subsingleton π)

/-- `homotopyEquiv_singleOne` is the subsingleton-cotangent concentration of `π`. -/
theorem homotopyEquiv_singleOne_eq {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] :
    homotopyEquiv_singleOne π =
      -- Local instance justification (noncanonical choice): the A'-algebra structure on A is π.
      letI : Algebra A' A := squareZeroAlgebra π
      Extension.NaiveCotangent.homotopyEquivSingleOneOfSubsingleton
        (squareZeroPresentation π).toExtension
        (squareZero_cotangentSpace_subsingleton π) :=
  sorry

/-- Linear comparison from the lifted conormal module of `π` to the square-zero kernel. -/
def squareZeroLiftToKernel {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] :
    squareZeroLift π →ₗ[A] kernelModule π where
  toFun x :=
    -- Local instance justification (noncanonical choice): the A'-algebra structure on A is π.
    letI : Algebra A' A := squareZeroAlgebra π
    ⟨constantCoeff
        (Function.surjInv Cotangent.mk_surjective
          ((Extension.NaiveCotangent.liftEquiv
            (squareZeroPresentation π).toExtension).toLinearMap x)).1,
      sorry⟩
  map_add' := sorry
  map_smul' := sorry

/-- `squareZeroLiftToKernel` evaluates a cotangent representative in the kernel of `π`. -/
theorem squareZeroLiftToKernel_apply {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] (x : squareZeroLift π) :
    (squareZeroLiftToKernel π x).1 =
      -- Local instance justification (noncanonical choice): the A'-algebra structure on A is π.
      letI : Algebra A' A := squareZeroAlgebra π
      constantCoeff
        (Function.surjInv Cotangent.mk_surjective
          ((Extension.NaiveCotangent.liftEquiv
            (squareZeroPresentation π).toExtension).toLinearMap x)).1 :=
  sorry

/-- Identification of the lifted conormal module of `π` with the square-zero kernel. -/
def squareZeroLiftEquiv {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] :
    squareZeroLift π ≃ₗ[A] kernelModule π :=
  LinearEquiv.ofBijective (squareZeroLiftToKernel π) sorry

/-- `squareZeroLiftEquiv` is induced by `squareZeroLiftToKernel`. -/
theorem squareZeroLiftEquiv_apply {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] (x : squareZeroLift π) :
    squareZeroLiftEquiv π x = squareZeroLiftToKernel π x :=
  sorry

/-- Source-changing comparison `NL{A⁄Λ} ⟶ NL{A⁄A'}` along `π`. -/
def toSquareZero {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A) :
    NL{A ⁄ Λ} ⟶ @Algebra.naiveCotangent A' A _ _ π.toRingHom.toAlgebra :=
  -- Local instance justification (noncanonical choice): the A'-algebra structure on A is π.
  letI : Algebra A' A := π.toRingHom.toAlgebra
  -- Local instance justification (noncanonical choice): the tower Λ → A' → A is induced by π.
  letI : IsScalarTower Λ A' A := IsScalarTower.of_algebraMap_eq' π.comp_algebraMap.symm
  NaiveCotangent.chainMap
    (Generators.defaultHom (Generators.self Λ A) (Generators.self A' A)).toExtensionHom

/-- `toSquareZero` is the default source-changing map of naive cotangent complexes. -/
theorem toSquareZero_eq {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A) :
    toSquareZero π =
      -- Local instance justification (noncanonical choice): the A'-algebra structure on A is π.
      letI : Algebra A' A := π.toRingHom.toAlgebra
      -- Local instance justification (noncanonical choice): the tower Λ → A' → A is induced by π.
      letI : IsScalarTower Λ A' A := IsScalarTower.of_algebraMap_eq' π.comp_algebraMap.symm
      NaiveCotangent.chainMap
        (Generators.defaultHom (Generators.self Λ A) (Generators.self A' A)).toExtensionHom :=
  sorry

/-- Target-changing comparison from the tensor model of `R` to `NL{A⁄Λ}`. -/
def toTarget {Λ ι A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    tensorModel J φ ⟶ Algebra.naiveCotangent Λ A :=
  -- Local instance justification (noncanonical choice): the A-algebra structure on the presented ring is the chosen deformation map φ.
  letI : Algebra (MvPolynomial ι Λ ⧸ J) A := φ.toRingHom.toAlgebra
  -- Local instance justification (noncanonical choice): the tower Λ → R → A is induced by φ.
  letI : IsScalarTower Λ (MvPolynomial ι Λ ⧸ J) A :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  (NaiveCotangent.BaseChange.scalarExtensionIsoTensorModel
      (presentation J).toExtension).inv ≫
    NaiveCotangent.ExtendScalars.map
      (Generators.defaultHom (presentation J) (Generators.self Λ A)).toExtensionHom

/-- `toTarget` is the default presentation map after scalar extension. -/
theorem toTarget_eq {Λ ι A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    toTarget J φ =
      -- Local instance justification (noncanonical choice): the A-algebra structure on the presented ring is the chosen deformation map φ.
      letI : Algebra (MvPolynomial ι Λ ⧸ J) A := φ.toRingHom.toAlgebra
      -- Local instance justification (noncanonical choice): the tower Λ → R → A is induced by φ.
      letI : IsScalarTower Λ (MvPolynomial ι Λ ⧸ J) A :=
        IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
      (NaiveCotangent.BaseChange.scalarExtensionIsoTensorModel
          (presentation J).toExtension).inv ≫
        NaiveCotangent.ExtendScalars.map
          (Generators.defaultHom (presentation J) (Generators.self Λ A)).toExtensionHom :=
  sorry

/-- The chain-level composite `NL{R⁄Λ} ⊗_R A ⟶ NL{A⁄Λ} ⟶ NL{A⁄A'} ⟶ I[1]`. -/
def compositionChain {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    tensorModel J φ ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.down ℕ) 1).obj
        (ModuleCat.of A (kernelModule π)) :=
  toTarget J φ ≫ toSquareZero π ≫
    (homotopyEquiv_squareZero π).hom ≫ (homotopyEquiv_singleOne π).hom ≫
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.down ℕ) 1).map
        (ModuleCat.ofHom (squareZeroLiftEquiv π).toLinearMap)

/-- The derived morphism `NL{R⁄Λ} ⊗_R A ⟶ I[1]` in `D(A)`. -/
public def composition {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    DerivedCategory.Q.obj ((tensorModel J φ).extend ComplexShape.embeddingDownNat) ⟶
      ((DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj
        (ModuleCat.of A (kernelModule π)))⟦(1 : ℤ)⟧ :=
  DerivedCategory.Q.map (HomologicalComplex.extendMap (compositionChain π J φ)
      ComplexShape.embeddingDownNat) ≫
    DerivedCategory.Q.map
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
        (ModuleCat.of A (kernelModule π)) 1 (-1 : ℤ) rfl).hom ≫
    ((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso (1 : ℤ) (-1) 0
      (add_neg_cancel (1 : ℤ))).inv.app (ModuleCat.of A (kernelModule π))

/-- `composition` is the derived image of `compositionChain`. -/
theorem composition_eq {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    composition π J φ =
      DerivedCategory.Q.map (HomologicalComplex.extendMap (compositionChain π J φ)
          ComplexShape.embeddingDownNat) ≫
        DerivedCategory.Q.map
          (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
            (ModuleCat.of A (kernelModule π)) 1 (-1 : ℤ) rfl).hom ≫
        ((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso (1 : ℤ) (-1) 0
          (add_neg_cancel (1 : ℤ))).inv.app (ModuleCat.of A (kernelModule π)) :=
  sorry

/-- The obstruction class equals the derived composition under the Ext identification. -/
theorem eq_composition {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    baseChangeExtEquiv π J φ (obstruction π J φ) = composition π J φ :=
  sorry

end

end Algebra.NaiveCotangent.Obstruction
