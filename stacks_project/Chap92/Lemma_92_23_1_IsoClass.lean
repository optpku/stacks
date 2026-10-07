module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import stacks_project.Chap91.Lemma_91_13_1_Diagram
public import stacks_project.Chap91.Lemma_91_13_3
public import stacks_project.Chap92.Definition_92_22_1_Morphism
public import stacks_project.Chap92.Lemma_92_22_4_NaiveCotangent
public import stacks_project.Chap92.Lemma_92_23_1_Obstruction

/-!
# Isomorphism classes of solutions of a first-order ringed-topoi equation

Two solutions of 92.23.0.1 are isomorphic when a morphism of middle ring sheaves fits the
identity diagram. Their classes are principal homogeneous under Ext⁽1⁾(Q NL[f], Q(G[0])),
via the same-site chart of 91.13.3 after inverse image along f.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits DerivedCategory
open CategoryTheory.Sheaf
open CategoryTheory.Sheaf.InternalCommRing
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening hiding Solution
open RingedSite.ToposHom
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

-- Local instance justification (defeq pin): moduleCategoryHasDerivedCategory is the reducible
-- standard HasDerivedCategory owner used by 92.22.3 and 91.13.*; Ext, Q, and singleFunctor must
-- share that instance.
attribute [local instance] moduleCategoryHasDerivedCategory
-- Local instance justification (defeq pin): moduleCat_hasDerivedCategory is reducible to
-- HasDerivedCategory.standard and is not global; ModuleDerived, singleFunctor, and Ext must share
-- that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

variable {O : Sheaf JC CommRingCat.{u}}
variable {OB OB' : Sheaf JD CommRingCat.{u}}
variable (t : OB' ⟶ OB) [IsFirstOrderThickening t]
variable (f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JD OB))
variable (G : SheafOfModules.{u} (ringSheaf JC O))
variable (c : inverseImageIdeal f t ⟶ (SheafOfModules.restrictScalars f.structureMap).obj G)
variable {t f G c}

/-- A morphism of middle ring sheaves fitting the identity diagram of two solutions of
92.23.0.1. -/
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
    -- Local instance justification (proof-local temporary data): kernel comparison needs
    -- `IsFirstOrderThickening` as a Prop field of each solution, not a global instance.
    letI := S₁.isFirstOrder
    letI := S₂.isFirstOrder
    inducedKernelMap S₁.π (𝟙 O) S₂.π hom comm_π ≫
        (SheafOfModules.Restriction.idIso' (ringSheafMap (𝟙 O))
          (ringSheafMap_id O)).inv.app (ideal S₂.π) ≫
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
      -- Local instance justification (proof-local temporary data): kernel comparison needs
      -- `IsFirstOrderThickening` as a Prop field of each solution, not a global instance.
      letI := S₁.isFirstOrder
      letI := S₂.isFirstOrder
      inducedKernelMap S₁.π (𝟙 O) S₂.π hom comm_π ≫
          (SheafOfModules.Restriction.idIso' (ringSheafMap (𝟙 O))
            (ringSheafMap_id O)).inv.app (ideal S₂.π) ≫
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
      S₁.fromInverseImage ≫ ringSheafMap φ.hom = S₂.fromInverseImage :=
  sorry

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
    (α : Ω(structureSheafMap f) ⟶ G) (U : Cᵒᵖ) (x : S.middle.obj.obj U) :
    (KernelIdeal.sheaf S.π).val.obj U :=
  -- Local instance justification (proof-local temporary data): `targetModuleForgetIso` needs
  -- `IsFirstOrderThickening S.π`, a Prop field of `Solution` that cannot be a global instance.
  letI := S.isFirstOrder
  ((inferInstance : IsFirstOrderThickening S.π).isSquareZero.targetModuleForgetIso
      inferInstance).hom.hom.app U
    (S.kernelIso.inv.val.app U
      (α.val.app U ((relativeDifferential (structureSheafMap f)).d (S.π.hom.app U x))))

/-- Square-zero inclusion of the perturbation section into the middle ring sheaf. -/
def perturbContribution (S : Solution t f G c)
    (α : Ω(structureSheafMap f) ⟶ G) (U : Cᵒᵖ) (x : S.middle.obj.obj U) :
    S.middle.obj.obj U :=
  -- Local instance justification (proof-local temporary data): `ιApp` needs
  -- `IsFirstOrderThickening S.π`, a Prop field of `Solution` that cannot be a global instance.
  letI := S.isFirstOrder
  KernelIdeal.ιApp S.π U (perturbKernelSection S α U x)

/-- The component ring homomorphism of a perturbed fitting automorphism. -/
def perturbRingHom (S : Solution t f G c) (α : Ω(structureSheafMap f) ⟶ G)
    (φ : SolutionIso S S) (U : Cᵒᵖ) :
    S.middle.obj.obj U →+* S.middle.obj.obj U where
  toFun x := φ.hom.hom.app U x + perturbContribution S α U x
  map_zero' := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry

/-- The structure-sheaf map of `φ`, modified by the square-zero inclusion of `α ∘ d`. -/
def perturbHom (S : Solution t f G c) (α : Ω(structureSheafMap f) ⟶ G)
    (φ : SolutionIso S S) : S.middle ⟶ S.middle :=
  ObjectProperty.homMk
    { app U := CommRingCat.ofHom (perturbRingHom S α φ U)
      naturality {U V} i := sorry }

/-- The action of `Hom(Ω(structureSheafMap f), G)` on automorphisms of a given solution. -/
def perturb (S : Solution t f G c) (α : Ω(structureSheafMap f) ⟶ G)
    (φ : SolutionIso S S) : SolutionIso S S :=
  SolutionIso.of (perturbHom S α φ) sorry sorry sorry

/-- `perturb` does not change the composite of the filling morphism with the projection. -/
theorem perturb_hom (S : Solution t f G c) (α : Ω(structureSheafMap f) ⟶ G)
    (φ : SolutionIso S S) : (perturb S α φ).hom ≫ S.π = φ.hom ≫ S.π :=
  sorry

/-- Kernel section measuring the difference of two fitting automorphisms. -/
def diffKernelSection (S : Solution t f G c) (φ φ' : SolutionIso S S)
    (U : Cᵒᵖ) (x : S.middle.obj.obj U) :
    (KernelIdeal.sheaf S.π).val.obj U :=
  -- Local instance justification (proof-local temporary data): `sectionsIso` needs
  -- `IsFirstOrderThickening S.π`, a Prop field of `Solution` that cannot be a global instance.
  letI := S.isFirstOrder
  (KernelIdeal.sectionsIso S.π U).inv
    ⟨φ'.hom.hom.app U x - φ.hom.hom.app U x, sorry⟩

/-- Additive sheaf map sending a middle-ring section to the `G`-valued difference of two
fitting automorphisms. -/
def diffAddHom (S : Solution t f G c) (φ φ' : SolutionIso S S) :
    (SheafOfModules.toSheaf (ringSheaf JC S.middle)).obj
        (SheafOfModules.unit (ringSheaf JC S.middle)) ⟶
      (SheafOfModules.toSheaf (ringSheaf JC O)).obj G :=
  -- Local instance justification (proof-local temporary data): kernel comparison needs
  -- `IsFirstOrderThickening S.π`, a Prop field of `Solution` that cannot be a global instance.
  letI := S.isFirstOrder
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun x :=
            S.kernelIso.hom.val.app U
              (((inferInstance : IsFirstOrderThickening S.π).isSquareZero.targetModuleForgetIso
                  inferInstance).inv.hom.app U
                (diffKernelSection S φ φ' U x))
          map_zero' := sorry
          map_add' := sorry }
      naturality {U V} i := sorry }

/-- The quotient projection `O' ⟶ O' / Ker(π)` is an epimorphism of additive sheaves. -/
instance solution_quotientProjection_epi (S : Solution t f G c) :
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
  CategoryTheory.Abelian.epiDesc
    (SheafOfModules.unitUnderlyingMap
      (ringSheafMap
        (IdealSheaf.Quotient.projection (KernelIdeal.subobject S.π))))
    (diffAddHom S φ φ')
    (diffAddHom_comp_quotientProjection S φ φ')

/-- Factorization of `diffAddHom` through the first-order quotient `O' / Ker(π) ≅ O`. -/
def diffOnO (S : Solution t f G c) (φ φ' : SolutionIso S S) :
    (SheafOfModules.toSheaf (ringSheaf JC O)).obj
        (SheafOfModules.unit (ringSheaf JC O)) ⟶
      (SheafOfModules.toSheaf (ringSheaf JC O)).obj G :=
  -- Local instance justification (proof-local temporary data): `quotientComparison_isIso`
  -- needs `IsFirstOrderThickening S.π`, a Prop field of `Solution` that cannot be a global
  -- instance.
  letI := S.isFirstOrder
  SheafOfModules.unitUnderlyingMap
      (ringSheafMap
        (KernelIdeal.quotientIso S.π (KernelIdeal.quotientComparison_isIso S.π)).inv) ≫
    diffOnQuotient S φ φ'

/-- The derivation of `O` classified by the difference of two fitting automorphisms. -/
def differenceDerivation (S : Solution t f G c) (φ φ' : SolutionIso S S) :
    SheafOfModules.RelativeDerivation (structureSheafMap f) G :=
  PresheafOfModules.Derivation'.mk
    (fun U ↦ ModuleCat.Derivation.mk
      (fun y ↦ (diffOnO S φ φ').hom.app U y)
      (fun _ _ ↦ sorry) (fun _ _ ↦ sorry) (fun _ ↦ sorry))
    (fun _ _ _ _ ↦ sorry)

/-- Difference of two fitting automorphisms, as a map out of `Ω(structureSheafMap f)`. -/
def diff (S : Solution t f G c) (φ φ' : SolutionIso S S) :
    Ω(structureSheafMap f) ⟶ G :=
  relativeDifferentialDesc (structureSheafMap f) (differenceDerivation S φ φ')

/-- `diff` recovers the unique map `Ω ⟶ G` comparing two fitting automorphisms. -/
theorem diff_spec (S : Solution t f G c) (φ φ' : SolutionIso S S) :
    perturb S (diff S φ φ') φ = φ' :=
  sorry

end SolutionIso

variable (t f G c)

/-- The setoid identifying solutions that admit a fitting isomorphism. -/
def isoSetoid : Setoid (Solution t f G c) where
  r S₁ S₂ := Nonempty (SolutionIso S₁ S₂)
  iseqv := sorry

/-- Two solutions are related iff a fitting isomorphism exists. -/
theorem isoSetoid_rel (S₁ S₂ : Solution t f G c) :
    isoSetoid t f G c S₁ S₂ ↔ Nonempty (SolutionIso S₁ S₂) :=
  sorry

/-- Isomorphism classes of solutions of a fixed diagram 92.23.0.1. -/
abbrev IsoClass := Quotient (isoSetoid t f G c)

/-- The isomorphism class of a given solution. -/
def isoClassMk (sol : Solution t f G c) : IsoClass t f G c :=
  Quotient.mk (isoSetoid t f G c) sol

/-- A fitting isomorphism identifies isomorphism classes. -/
theorem isoClassMk_eq_of_iso {S₁ S₂ : Solution t f G c} (φ : SolutionIso S₁ S₂) :
    isoClassMk t f G c S₁ = isoClassMk t f G c S₂ :=
  sorry

/-- Forgetting commutativity of inverse image along `f` recovers the bundled ring-valued
inverse image. -/
def inverseImageCommRing_ring (R : Sheaf JD CommRingCat.{u}) :
    ringSheaf JC ((inverseImageCommRing f).obj R) ≅
      f.toTopos.ringInverseImage.obj (ringSheaf JD R) :=
  Iso.refl _

/-- The inverse-image structure map of a two-site solution, as a commutative ring-sheaf
morphism. -/
def fromInverseImageComm (S : Solution t f G c) :
    (inverseImageCommRing f).obj OB' ⟶ S.middle :=
  InternalCommRing.CommRingSheaves.fullyFaithfulForgetRing.preimage
    ((inverseImageCommRing_ring f OB').hom ≫ S.fromInverseImage)

/-- Convert a two-site solution to the same-site 91.13.0.1 solution of the pulled thickening. -/
def toSameSite (S : Solution t f G c) :
    SheafOfModules.RingedSite.FirstOrderThickening.Solution
      (pulledThickening t f) (pulled_isFirstOrderThickening t f).isSquareZero
      (structureSheafMap f) G (coeffSameSite t f G c) :=
  -- Local instance justification (proof-local temporary data): `quotientComparison_isIso`
  -- needs `IsFirstOrderThickening S.π`, a Prop field of `Solution` that cannot be a global
  -- instance.
  letI := S.isFirstOrder
  { middle := S.middle
    proj := S.π
    structureMap := fromInverseImageComm t f G c S
    proj_locallySurjective := S.isFirstOrder.isLocallySurjective
    proj_squareZero := S.isFirstOrder.isSquareZero
    proj_quotient_isIso := KernelIdeal.quotientComparison_isIso S.π
    commutes := sorry
    kernelIso := S.kernelIso
    induces_c := sorry }

/-- Convert a same-site 91.13.0.1 solution of the pulled thickening to a two-site solution. -/
def fromSameSite
    (S : SheafOfModules.RingedSite.FirstOrderThickening.Solution
      (pulledThickening t f) (pulled_isFirstOrderThickening t f).isSquareZero
      (structureSheafMap f) G (coeffSameSite t f G c)) :
    Solution t f G c :=
  -- Local instance justification (proof-local temporary data): two-site `Solution.of` needs
  -- `IsFirstOrderThickening S.proj` from the stored 91.13 fields, not a global instance.
  letI : IsFirstOrderThickening S.proj :=
    { isLocallySurjective := S.proj_locallySurjective
      isSquareZero := S.proj_squareZero }
  Solution.of t f G c S.middle S.proj
    ((inverseImageCommRing_ring f OB').inv ≫ ringSheafMap S.structureMap) sorry
    ((SheafOfModules.RingedSite.FirstOrderThickening.Solution.idealTargetIso S).trans
      S.kernelIso) sorry

/-- Isomorphism classes of two-site solutions are identified with same-site classes of the
pulled thickening. -/
def isoClassCongr :
    SheafOfModules.RingedSite.FirstOrderThickening.Solution.IsoClass
      (pulledThickening t f) (pulled_isFirstOrderThickening t f).isSquareZero
      (structureSheafMap f) G (coeffSameSite t f G c) ≃
      IsoClass t f G c where
  toFun := Quotient.map (fromSameSite t f G c) sorry
  invFun := Quotient.map (toSameSite t f G c) sorry
  left_inv := sorry
  right_inv := sorry

/-- The naive Ext¹ chart of isomorphism classes, via the 91.13.3 chart of the pulled
thickening. -/
def isoClassNaiveEquiv (S0 : Solution t f G c) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj NL[f], coeffSingle G) ≃ IsoClass t f G c :=
  (SheafOfModules.RingedSite.FirstOrderThickening.Solution.isoClassEquiv
      (toSameSite t f G c S0)).trans
    (isoClassCongr t f G c)

/-- The based naive chart sends an Ext¹ class to the translate of the basepoint. -/
theorem isoClassNaiveEquiv_apply (S0 : Solution t f G c)
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj NL[f], coeffSingle G)) :
    isoClassNaiveEquiv t f G c S0 ξ =
      isoClassCongr t f G c
        (SheafOfModules.RingedSite.FirstOrderThickening.Solution.isoClassEquiv
          (toSameSite t f G c S0) ξ) :=
  sorry

/-- The zero Ext¹ class is sent to the class of the basepoint. -/
theorem isoClassNaiveEquiv_zero (S0 : Solution t f G c) :
    isoClassNaiveEquiv t f G c S0 0 = isoClassMk t f G c S0 :=
  sorry

/-- The inverse naive chart is the 91.13.3 inverse, transported along `isoClassCongr`. -/
theorem isoClassNaiveEquiv_symm_apply (S0 : Solution t f G c) (p : IsoClass t f G c) :
    (isoClassNaiveEquiv t f G c S0).symm p =
      (SheafOfModules.RingedSite.FirstOrderThickening.Solution.isoClassEquiv
          (toSameSite t f G c S0)).symm
        ((isoClassCongr t f G c).symm p) :=
  sorry

end RingedSite.FirstOrderThickening
