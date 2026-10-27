/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.FittingMap
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.CotangentComplex
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.FirstOrderThickening.Solution
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.Ext
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Fitting isomorphisms of first-order deformations

Maps preserving the quotient, structure map, and identified kernel admit explicit
composition and inversion. Their automorphisms are classified by cotangent Ext⁰.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits DerivedCategory
open CategoryTheory.Sheaf
open CategoryTheory.Sheaf.InternalCommRing
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening (ideal inducedKernelMap)
open RingedSite.ToposHom
open SheafOfModules.RingedSite.CotangentComplex (coeffSingle extZeroHomEquiv)
open scoped DerivedExt RingedSite.ToposHom SheafOfModules.RingedSite

namespace RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JC.HasSheafCompose (forget RingCat.{u})]
variable [JD.HasSheafCompose (forget RingCat.{u})]
variable [JC.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [JD.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [JC.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [JD.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify JC CommRingCat.{u}]
variable [HasWeakSheafify JD CommRingCat.{u}]
variable [JC.WEqualsLocallyBijective CommRingCat.{u}]
variable [JD.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable [UnivLE.{u, u}]

-- Local instance justification (defeq pin): pin Q, singleFunctor, and Ext to the reducible standard derived category of the site-presented module category.
attribute [local instance] moduleCategoryHasDerivedCategory
-- Local instance justification (defeq pin): pin ModuleDerived and site-presented Ext to the same standard derived-category localization.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

variable {O : Sheaf JC CommRingCat.{u}}
variable {OB OB' : Sheaf JD CommRingCat.{u}}
variable (t : OB' ⟶ OB) [IsFirstOrderThickening t]
variable (f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JD OB))
variable (G : SheafOfModules.{u} (ringSheaf JC O))
variable (c : inverseImageIdeal f t ⟶ (SheafOfModules.restrictScalars f.structureMap).obj G)
variable {t f G c}

/-- A morphism of middle ring sheaves fitting the identity diagram of two solutions of
the fixed deformation equation. -/
structure SolutionIso (S₁ S₂ : Solution t f G c) where
  /-- The filling morphism of middle ring sheaves `O'₁ ⟶ O'₂`. -/
  hom : S₁.middle ⟶ S₂.middle
  /-- The filling morphism is compatible with the projections onto `O`. -/
  comm_π : hom ≫ S₂.π = S₁.π ≫ 𝟙 O
  /-- The filling morphism is compatible with the structure maps from `f⁻¹O_{B'}`. -/
  comm_fromInverseImage :
    S₁.fromInverseImage ≫ ringSheafMap hom = S₂.fromInverseImage
  /-- The filling morphism induces the identification of kernels with `G`. -/
  induces :
    @inducedKernelMap _ _ _ _ _ _ _ _ _ _ _ _ _ S₁.π (𝟙 O) S₂.π hom
      S₁.isFirstOrder S₂.isFirstOrder comm_π ≫
        (SheafOfModules.Restriction.idIso' (ringSheafMap (𝟙 O))
          (ringSheafMap_id O)).inv.app (ideal S₂.π (hπ := S₂.isFirstOrder)) ≫
        S₂.kernelIso.hom =
      S₁.kernelIso.hom

namespace SolutionIso

/-- Assemble a fitting isomorphism from a morphism of middle ring sheaves and the three
compatibility conditions. -/
def of {S₁ S₂ : Solution t f G c} (hom : S₁.middle ⟶ S₂.middle)
    (comm_π : hom ≫ S₂.π = S₁.π ≫ 𝟙 O)
    (comm_fromInverseImage :
      S₁.fromInverseImage ≫ ringSheafMap hom = S₂.fromInverseImage)
    (induces :
      @inducedKernelMap _ _ _ _ _ _ _ _ _ _ _ _ _ S₁.π (𝟙 O) S₂.π hom
        S₁.isFirstOrder S₂.isFirstOrder comm_π ≫
          (SheafOfModules.Restriction.idIso' (ringSheafMap (𝟙 O))
            (ringSheafMap_id O)).inv.app (ideal S₂.π (hπ := S₂.isFirstOrder)) ≫
          S₂.kernelIso.hom =
        S₁.kernelIso.hom) :
    SolutionIso S₁ S₂ where
  hom := hom
  comm_π := comm_π
  comm_fromInverseImage := comm_fromInverseImage
  induces := induces

/-- A fitting isomorphism is compatible with the projections onto `O`, the maps from
`f⁻¹O_{B'}`, and the kernel identifications with `G`. -/
theorem spec {S₁ S₂ : Solution t f G c} (φ : SolutionIso S₁ S₂) :
    φ.hom ≫ S₂.π = S₁.π ∧
      S₁.fromInverseImage ≫ ringSheafMap φ.hom = S₂.fromInverseImage ∧
      (@inducedKernelMap _ _ _ _ _ _ _ _ _ _ _ _ _ S₁.π (𝟙 O) S₂.π φ.hom
        S₁.isFirstOrder S₂.isFirstOrder φ.comm_π) ≫
          (SheafOfModules.Restriction.idIso' (ringSheafMap (𝟙 O))
            (ringSheafMap_id O)).inv.app (ideal S₂.π (hπ := S₂.isFirstOrder)) ≫
          S₂.kernelIso.hom = S₁.kernelIso.hom := sorry

/-- The middle-ring map of a fitting morphism is invertible. -/
theorem isIso_hom {S₁ S₂ : Solution t f G c} (φ : SolutionIso S₁ S₂) :
    IsIso φ.hom := sorry

/-- Composition of fitting isomorphisms is composition of their middle-ring maps. -/
def comp {S₁ S₂ S₃ : Solution t f G c}
    (φ : SolutionIso S₁ S₂) (ψ : SolutionIso S₂ S₃) : SolutionIso S₁ S₃ where
  hom := φ.hom ≫ ψ.hom
  comm_π := sorry
  comm_fromInverseImage := sorry
  induces := sorry

/-- The inverse fitting isomorphism has the inverse middle-ring map. -/
def inv {S₁ S₂ : Solution t f G c} (φ : SolutionIso S₁ S₂) : SolutionIso S₂ S₁ where
  hom := CategoryTheory.inv φ.hom (I := isIso_hom φ)
  comm_π := sorry
  comm_fromInverseImage := sorry
  induces := sorry

/-- The identity automorphism of a solution. -/
def idAuto (S : Solution t f G c) : SolutionIso S S where
  hom := 𝟙 S.middle
  comm_π := sorry
  comm_fromInverseImage := sorry
  induces := sorry

/-- The underlying morphism of `idAuto` is the identity on the middle ring sheaf. -/
theorem idAuto_hom (S : Solution t f G c) : (idAuto S).hom = 𝟙 S.middle :=
  sorry

/-- Kernel section of a perturbation of a fitting automorphism, obtained by evaluating
`α ∘ d` on the projection of a section of the middle ring sheaf. -/
def perturbKernelSection (S : Solution t f G c)
    (α : Ω(commRingStructureMap f) ⟶ G) (U : Cᵒᵖ) (x : S.middle.obj.obj U) :
    (KernelIdeal.sheaf S.π).val.obj U :=
  (S.isFirstOrder.isSquareZero.targetModuleForgetIso
      (@KernelIdeal.quotientComparison_isIso _ _ _ _ _ _ _ S.π _
        S.isFirstOrder.isLocallySurjective)).hom.hom.app U
    (S.kernelIso.inv.val.app U
      (α.val.app U ((relativeDifferential (commRingStructureMap f)).d (S.π.hom.app U x))))

/-- Square-zero inclusion of the perturbation section into the middle ring sheaf. -/
def perturbContribution (S : Solution t f G c)
    (α : Ω(commRingStructureMap f) ⟶ G) (U : Cᵒᵖ) (x : S.middle.obj.obj U) :
    S.middle.obj.obj U :=
  KernelIdeal.ιApp S.π U (perturbKernelSection S α U x)

/-- The component ring homomorphism of a perturbed fitting automorphism. -/
def perturbRingHom (S : Solution t f G c) (α : Ω(commRingStructureMap f) ⟶ G)
    (φ : SolutionIso S S) (U : Cᵒᵖ) :
    S.middle.obj.obj U →+* S.middle.obj.obj U where
  toFun x := φ.hom.hom.app U x + perturbContribution S α U x
  map_zero' := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry

/-- The structure-sheaf map of `φ`, modified by the square-zero inclusion of `α ∘ d`. -/
def perturbHom (S : Solution t f G c) (α : Ω(commRingStructureMap f) ⟶ G)
    (φ : SolutionIso S S) : S.middle ⟶ S.middle :=
  ObjectProperty.homMk
    { app U := CommRingCat.ofHom (perturbRingHom S α φ U)
      naturality {U V} i := sorry }

/-- The action of `Hom(Ω(commRingStructureMap f), G)` on automorphisms of a given solution. -/
def perturb (S : Solution t f G c) (α : Ω(commRingStructureMap f) ⟶ G)
    (φ : SolutionIso S S) : SolutionIso S S :=
  SolutionIso.of (perturbHom S α φ) sorry sorry sorry

/-- `perturb` does not change the composite of the filling morphism with the projection. -/
theorem perturb_hom (S : Solution t f G c) (α : Ω(commRingStructureMap f) ⟶ G)
    (φ : SolutionIso S S) : (perturb S α φ).hom ≫ S.π = φ.hom ≫ S.π :=
  sorry

/-- Kernel section measuring the difference of two fitting automorphisms. -/
def diffKernelSection (S : Solution t f G c) (φ φ' : SolutionIso S S)
    (U : Cᵒᵖ) (x : S.middle.obj.obj U) :
    (KernelIdeal.sheaf S.π).val.obj U :=
  (KernelIdeal.sectionsIso S.π U).inv
    ⟨φ'.hom.hom.app U x - φ.hom.hom.app U x, sorry⟩

/-- Additive sheaf map sending a middle-ring section to the `G`-valued difference of two
fitting automorphisms. -/
def diffAddHom (S : Solution t f G c) (φ φ' : SolutionIso S S) :
    (SheafOfModules.toSheaf (ringSheaf JC S.middle)).obj
        (SheafOfModules.unit (ringSheaf JC S.middle)) ⟶
      (SheafOfModules.toSheaf (ringSheaf JC O)).obj G :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun x :=
            S.kernelIso.hom.val.app U
              ((S.isFirstOrder.isSquareZero.targetModuleForgetIso
                  (@KernelIdeal.quotientComparison_isIso _ _ _ _ _ _ _ S.π _
                    S.isFirstOrder.isLocallySurjective)).inv.hom.app U
                (diffKernelSection S φ φ' U x))
          map_zero' := sorry
          map_add' := sorry }
      naturality {U V} i := sorry }

/-- The quotient projection `O' ⟶ O' / Ker(π)` is an epimorphism of additive sheaves. -/
theorem solution_quotientProjection_epi (S : Solution t f G c) :
    Epi (SheafOfModules.unitUnderlyingMap
      (ringSheafMap
        (IdealSheaf.Quotient.projection (KernelIdeal.subobject S.π)))) :=
  sorry

/-- `diffAddHom` vanishes on the kernel of the quotient projection of `S.π`. -/
theorem diffAddHom_comp_quotientProjection (S : Solution t f G c)
    (φ φ' : SolutionIso S S) :
    kernel.ι
        (SheafOfModules.unitUnderlyingMap
          (ringSheafMap
            (IdealSheaf.Quotient.projection (KernelIdeal.subobject S.π)))) ≫
      diffAddHom S φ φ' = 0 :=
  sorry

/-- Descent of `diffAddHom` through the quotient projection `O' ⟶ O' / Ker(π)`. -/
def diffOnQuotient (S : Solution t f G c) (φ φ' : SolutionIso S S) :
    (SheafOfModules.toSheaf
        (ringSheaf JC (IdealSheaf.Quotient.sheaf (KernelIdeal.subobject S.π)))).obj
      (SheafOfModules.unit
        (ringSheaf JC (IdealSheaf.Quotient.sheaf (KernelIdeal.subobject S.π)))) ⟶
      (SheafOfModules.toSheaf (ringSheaf JC O)).obj G :=
  @CategoryTheory.Abelian.epiDesc _ _ _ _ _
    (SheafOfModules.unitUnderlyingMap
      (ringSheafMap
        (IdealSheaf.Quotient.projection (KernelIdeal.subobject S.π))))
    (solution_quotientProjection_epi S) _
    (diffAddHom S φ φ') (diffAddHom_comp_quotientProjection S φ φ')

/-- Factorization of `diffAddHom` through the first-order quotient `O' / Ker(π) ≅ O`. -/
def diffOnO (S : Solution t f G c) (φ φ' : SolutionIso S S) :
    (SheafOfModules.toSheaf (ringSheaf JC O)).obj
        (SheafOfModules.unit (ringSheaf JC O)) ⟶
      (SheafOfModules.toSheaf (ringSheaf JC O)).obj G :=
  SheafOfModules.unitUnderlyingMap
      (ringSheafMap
        (KernelIdeal.quotientIso S.π (@KernelIdeal.quotientComparison_isIso _ _ _ _ _ _ _ S.π _
        S.isFirstOrder.isLocallySurjective)).inv) ≫
    diffOnQuotient S φ φ'

/-- The derivation of `O` classified by the difference of two fitting automorphisms. -/
def differenceDerivation (S : Solution t f G c) (φ φ' : SolutionIso S S) :
    SheafOfModules.RelativeDerivation (commRingStructureMap f) G :=
  PresheafOfModules.Derivation'.mk
    (fun U ↦ ModuleCat.Derivation.mk
      (fun y ↦ (diffOnO S φ φ').hom.app U y)
      (fun _ _ ↦ sorry) (fun _ _ ↦ sorry) (fun _ ↦ sorry))
    (fun _ _ _ _ ↦ sorry)

/-- Difference of two fitting automorphisms, as a map out of `Ω(commRingStructureMap f)`. -/
def diff (S : Solution t f G c) (φ φ' : SolutionIso S S) :
    Ω(commRingStructureMap f) ⟶ G :=
  relativeDifferentialDesc (commRingStructureMap f) (differenceDerivation S φ φ')

/-- `diff` recovers the unique map `Ω ⟶ G` comparing two fitting automorphisms. -/
theorem diff_spec (S : Solution t f G c) (φ φ' : SolutionIso S S) :
    perturb S (diff S φ φ') φ = φ' :=
  sorry

end SolutionIso

variable (t f G c)

/-- Fitting automorphisms of a solution are canonically identified with cotangent Ext⁰. -/
def autEquiv (S : Solution t f G c) :
    Ext⁽(0 : ℤ)⁾(DerivedCategory.Q.obj (commRingCotangentComplex f), coeffSingle G) ≃
      SolutionIso S S where
  toFun e :=
    SolutionIso.perturb S ((extZeroHomEquiv (commRingStructureMap f) G).symm e)
      (SolutionIso.idAuto S)
  invFun φ :=
    extZeroHomEquiv (commRingStructureMap f) G (SolutionIso.diff S (SolutionIso.idAuto S) φ)
  left_inv := sorry
  right_inv := sorry

/-- The forward map of `autEquiv` sends an Ext⁰ class to the perturbation of `idAuto`. -/
theorem autEquiv_apply (S : Solution t f G c)
    (e : Ext⁽(0 : ℤ)⁾(DerivedCategory.Q.obj (commRingCotangentComplex f), coeffSingle G)) :
    autEquiv t f G c S e =
      SolutionIso.perturb S ((extZeroHomEquiv (commRingStructureMap f) G).symm e)
        (SolutionIso.idAuto S) :=
  sorry

end RingedSite.FirstOrderThickening
