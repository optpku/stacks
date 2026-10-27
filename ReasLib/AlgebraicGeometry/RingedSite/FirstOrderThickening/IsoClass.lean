/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Torsor.Defs
public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.Difference
public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.Translate
public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.MapObstruction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Identity

/-!
# Isomorphism classes and translations of fixed square-zero extensions

Common-presentation differences and graph-quotient translations describe the additive torsor
of extension classes. The representative presentations and the certificates for their specified
maps are explicit inputs. Inverse-image and derived-pullback comparisons use canonical
library constructions; an explicit-data formulation of their preservation laws is a further
refinement of those foundations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.NaiveCotangent
open scoped DerivedExt SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace FirstOrderThickening
namespace Solution

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, and Ext must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation uses the same standard derived-category owner, exposed through the site-level spelling.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {O_B' O_B O : Sheaf J CommRingCat.{u}}
variable {π : O_B' ⟶ O_B} [Sheaf.IsLocallySurjective π]
variable {hπ : KernelIdeal.IsSquareZero π}
variable {fSharp : O_B ⟶ O}
variable {G : SheafOfModules (ringSheaf J O)}
variable {c :
    hπ.targetModule (KernelIdeal.quotientComparison_isIso π) ⟶
      (restrictionAlong fSharp).obj G}

/-- The base thickening `π` is first-order, via the square-zero witness of the equation. -/
@[reducible]
def instIsFirstOrderThickening_π : IsFirstOrderThickening π where
  isLocallySurjective := inferInstance
  isSquareZero := hπ

/-- A solution supplies a first-order thickening `proj : O' ⟶ O`. -/
@[reducible] def instIsFirstOrderThickening_sol (sol : Solution π hπ fSharp G c) :
    IsFirstOrderThickening sol.proj where
  isLocallySurjective := sol.proj_locallySurjective
  isSquareZero := sol.proj_squareZero

/-- The first-order kernel module of `sol.proj` agrees with the stored square-zero target
module of `sol`. -/
def idealTargetIso (sol : Solution π hπ fSharp G c) :
    (ideal sol.proj (hπ := instIsFirstOrderThickening_sol sol)) ≅ sol.proj_squareZero.targetModule sol.proj_quotient_isIso where
  hom :=
    ⟨PresheafOfModules.homMk
      ((sheafToPresheaf J AddCommGrpCat.{u}).map
        ((sol.proj_squareZero.targetModuleForgetIso
            (@KernelIdeal.quotientComparison_isIso _ _ _ _ _ _ _ sol.proj _ sol.proj_locallySurjective)).hom ≫
          (sol.proj_squareZero.targetModuleForgetIso sol.proj_quotient_isIso).inv))
      (fun _ _ _ ↦ sorry)⟩
  inv :=
    ⟨PresheafOfModules.homMk
      ((sheafToPresheaf J AddCommGrpCat.{u}).map
        ((sol.proj_squareZero.targetModuleForgetIso sol.proj_quotient_isIso).hom ≫
          (sol.proj_squareZero.targetModuleForgetIso
            (@KernelIdeal.quotientComparison_isIso _ _ _ _ _ _ _ sol.proj _ sol.proj_locallySurjective)).inv))
      (fun _ _ _ ↦ sorry)⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underlying additive map of `idealTargetIso` is the composite of the two
`targetModuleForgetIso`s. -/
theorem idealTargetIso_toSheaf (sol : Solution π hπ fSharp G c) :
    (SheafOfModules.toSheaf (ringSheaf J O)).map (idealTargetIso sol).hom =
      (sol.proj_squareZero.targetModuleForgetIso
          (@KernelIdeal.quotientComparison_isIso _ _ _ _ _ _ _ sol.proj _ sol.proj_locallySurjective)).hom ≫
        (sol.proj_squareZero.targetModuleForgetIso sol.proj_quotient_isIso).inv := sorry

/-- Kernel identification of a solution, as a map `(ideal sol.proj (hπ := instIsFirstOrderThickening_sol sol)) ⟶ 𝒢`. -/
def kernelIdealHom (sol : Solution π hπ fSharp G c) :
    (ideal sol.proj (hπ := instIsFirstOrderThickening_sol sol)) ⟶ G :=
  (idealTargetIso sol).hom ≫ sol.kernelIso.hom

/-- `kernelIdealHom` is `idealTargetIso` followed by `kernelIso`. -/
theorem kernelIdealHom_spec (sol : Solution π hπ fSharp G c) :
    kernelIdealHom sol = (idealTargetIso sol).hom ≫ sol.kernelIso.hom := sorry

/-- The identity connecting cube comparing two solutions of the same equation, with
front face `S₁`, back face `S₂`, and `g = 𝟙 O`. -/
def compare (S₁ S₂ : Solution π hπ fSharp G c) :
    -- Local instance justification (noncanonical choice): RelativeDiagram and its FittingMap and obstruction APIs consume the fixed square-zero witness hπ through first-order thickening class arguments.
    letI := instIsFirstOrderThickening_π (hπ := hπ)
    RelativeDiagram S₁.proj π S₂.proj π
      (hπO1 := instIsFirstOrderThickening_sol S₁)
      (hπO2 := instIsFirstOrderThickening_sol S₂) :=
  -- Local instance justification (noncanonical choice): RelativeDiagram and its FittingMap and obstruction APIs consume the fixed square-zero witness hπ through first-order thickening class arguments.
  letI := instIsFirstOrderThickening_π (hπ := hπ)
  RelativeDiagram.of
    (hπO1 := instIsFirstOrderThickening_sol S₁)
    (hπO2 := instIsFirstOrderThickening_sol S₂) fSharp S₁.structureMap S₁.commutes fSharp S₂.structureMap S₂.commutes
    (𝟙 O) (𝟙 O_B) (𝟙 O_B')
    ((Category.id_comp π).trans (Category.comp_id π).symm)
    ((Category.id_comp fSharp).trans (Category.comp_id fSharp).symm)
    ((idealTargetIso S₁).hom ≫ S₁.kernelIso.hom ≫ S₂.kernelIso.inv ≫
      (idealTargetIso S₂).inv ≫
        (SheafOfModules.Restriction.idIso' (ringSheafMap (𝟙 O))
          (ringSheafMap_id O)).hom.app ((ideal S₂.proj (hπ := instIsFirstOrderThickening_sol S₂))))
    sorry

/-- The identity connecting cube has identity maps on `O`, `O_B`, and `O_{B'}`, and `ν` is
the identity-restriction composite of the two kernel identifications. -/
theorem compare_spec (S₁ S₂ : Solution π hπ fSharp G c) :
    -- Local instance justification (noncanonical choice): RelativeDiagram and its FittingMap and obstruction APIs consume the fixed square-zero witness hπ through first-order thickening class arguments.
    letI := instIsFirstOrderThickening_π (hπ := hπ)
    (compare S₁ S₂).f1 (hπO1 := instIsFirstOrderThickening_sol S₁)
        (hπO2 := instIsFirstOrderThickening_sol S₂) = fSharp ∧
      (compare S₁ S₂).f2 (hπO1 := instIsFirstOrderThickening_sol S₁)
        (hπO2 := instIsFirstOrderThickening_sol S₂) = fSharp ∧
      (compare S₁ S₂).f1' (hπO1 := instIsFirstOrderThickening_sol S₁)
        (hπO2 := instIsFirstOrderThickening_sol S₂) = S₁.structureMap ∧
      (compare S₁ S₂).f2' (hπO1 := instIsFirstOrderThickening_sol S₁)
        (hπO2 := instIsFirstOrderThickening_sol S₂) = S₂.structureMap ∧
      (compare S₁ S₂).g (hπO1 := instIsFirstOrderThickening_sol S₁)
        (hπO2 := instIsFirstOrderThickening_sol S₂) = 𝟙 O ∧
      (compare S₁ S₂).t (hπO1 := instIsFirstOrderThickening_sol S₁)
        (hπO2 := instIsFirstOrderThickening_sol S₂) = 𝟙 O_B ∧
      (compare S₁ S₂).t' (hπO1 := instIsFirstOrderThickening_sol S₁)
        (hπO2 := instIsFirstOrderThickening_sol S₂) = 𝟙 O_B' ∧
      (compare S₁ S₂).ν (hπO1 := instIsFirstOrderThickening_sol S₁)
        (hπO2 := instIsFirstOrderThickening_sol S₂) =
        (idealTargetIso S₁).hom ≫ S₁.kernelIso.hom ≫ S₂.kernelIso.inv ≫
          (idealTargetIso S₂).inv ≫
            (SheafOfModules.Restriction.idIso' (ringSheafMap (𝟙 O))
              (ringSheafMap_id O)).hom.app ((ideal S₂.proj (hπ := instIsFirstOrderThickening_sol S₂))) := sorry

/-- The setoid identifying solutions that admit a fitting map of `compare`. -/
def isoSetoid (π : O_B' ⟶ O_B) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π) (fSharp : O_B ⟶ O)
    (G : SheafOfModules (ringSheaf J O))
    (c : hπ.targetModule (KernelIdeal.quotientComparison_isIso π) ⟶
      (restrictionAlong fSharp).obj G) :
    Setoid (Solution π hπ fSharp G c) where
  r S₁ S₂ :=
    -- Local instance justification (noncanonical choice): RelativeDiagram and its FittingMap and obstruction APIs consume the fixed square-zero witness hπ through first-order thickening class arguments.
    letI := instIsFirstOrderThickening_π (hπ := hπ)
    Nonempty (FittingMap (compare S₁ S₂)
      (hπO1 := instIsFirstOrderThickening_sol S₁)
      (hπO2 := instIsFirstOrderThickening_sol S₂))
  iseqv := sorry

/-- Two solutions are related iff the identity cube admits a fitting map. -/
theorem isoSetoid_rel (S₁ S₂ : Solution π hπ fSharp G c) :
    -- Local instance justification (noncanonical choice): RelativeDiagram and its FittingMap and obstruction APIs consume the fixed square-zero witness hπ through first-order thickening class arguments.
    letI := instIsFirstOrderThickening_π (hπ := hπ)
    isoSetoid π hπ fSharp G c S₁ S₂ ↔ Nonempty (FittingMap (compare S₁ S₂)
      (hπO1 := instIsFirstOrderThickening_sol S₁)
      (hπO2 := instIsFirstOrderThickening_sol S₂)) := sorry

/-- Isomorphism classes of solutions of a fixed extension diagram. -/
abbrev IsoClass (π : O_B' ⟶ O_B) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π) (fSharp : O_B ⟶ O)
    (G : SheafOfModules (ringSheaf J O))
    (c : hπ.targetModule (KernelIdeal.quotientComparison_isIso π) ⟶
      (restrictionAlong fSharp).obj G) :=
  Quotient (isoSetoid π hπ fSharp G c)

/-- The isomorphism class of a given solution. -/
def isoClassMk (sol : Solution π hπ fSharp G c) : IsoClass π hπ fSharp G c :=
  Quotient.mk (isoSetoid π hπ fSharp G c) sol

/-- A fitting map of the identity cube identifies isomorphism classes. -/
theorem isoClassMk_eq_mk_of_hom {S₁ S₂ : Solution π hπ fSharp G c}
    (φ :
      -- Local instance justification (noncanonical choice): FittingMap consumes the fixed square-zero witness hπ through its first-order thickening class argument.
      letI := instIsFirstOrderThickening_π (hπ := hπ)
      FittingMap (compare S₁ S₂)
      (hπO1 := instIsFirstOrderThickening_sol S₁)
      (hπO2 := instIsFirstOrderThickening_sol S₂)) :
    isoClassMk S₁ = isoClassMk S₂ := sorry

/-- The obstruction class o(O'₁, O'₂) in Ext⁽1⁾(Q NL(fSharp), Q(𝒢[0])), obtained by
transporting `mapObstruction` of the identity cube along L(𝟙 O)^* ≅ id and the
back kernel identification. -/
def obstruction (S₁ S₂ : Solution π hπ fSharp G c) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  -- Local instance justification (noncanonical choice): RelativeDiagram and its FittingMap and obstruction APIs consume the fixed square-zero witness hπ through first-order thickening class arguments.
  letI := instIsFirstOrderThickening_π (hπ := hπ)
  (SameSite.pullbackDerived.idIso O).inv.app
      (DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp))) ≫
    mapObstruction (compare S₁ S₂)
      (hπO1 := instIsFirstOrderThickening_sol S₁)
      (hπO2 := instIsFirstOrderThickening_sol S₂) ≫
      (shiftFunctor (DerivedCategory (ringedSiteModuleCategory.{u, u, u, u} J O)) (1 : ℤ)).map
        (DerivedCategory.Q.map
          ((CochainComplex.singleFunctor
              (ringedSiteModuleCategory.{u, u, u, u} J O) 0).map
            (kernelIdealHom S₂)))

/-- `obstruction` is `mapObstruction` of `compare`, transported to
Ext⁽1⁾(Q NL(fSharp), Q(𝒢[0])). -/
theorem obstruction_spec (S₁ S₂ : Solution π hπ fSharp G c) :
    -- Local instance justification (noncanonical choice): RelativeDiagram and its FittingMap and obstruction APIs consume the fixed square-zero witness hπ through first-order thickening class arguments.
    letI := instIsFirstOrderThickening_π (hπ := hπ)
    obstruction S₁ S₂ =
      (SameSite.pullbackDerived.idIso O).inv.app
          (DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp))) ≫
        mapObstruction (compare S₁ S₂)
      (hπO1 := instIsFirstOrderThickening_sol S₁)
      (hπO2 := instIsFirstOrderThickening_sol S₂) ≫
          (shiftFunctor
              (DerivedCategory (ringedSiteModuleCategory.{u, u, u, u} J O)) (1 : ℤ)).map
            (DerivedCategory.Q.map
              ((CochainComplex.singleFunctor
                  (ringedSiteModuleCategory.{u, u, u, u} J O) 0).map
                (kernelIdealHom S₂))) := sorry

/-- The obstruction vanishes if and only if the identity cube admits a fitting map. -/
theorem obstruction_eq_zero_iff (S₁ S₂ : Solution π hπ fSharp G c) :
    -- Local instance justification (noncanonical choice): RelativeDiagram and its FittingMap and obstruction APIs consume the fixed square-zero witness hπ through first-order thickening class arguments.
    letI := instIsFirstOrderThickening_π (hπ := hπ)
    obstruction S₁ S₂ = 0 ↔ Nonempty (FittingMap (compare S₁ S₂)
      (hπO1 := instIsFirstOrderThickening_sol S₁)
      (hπO2 := instIsFirstOrderThickening_sol S₂)) := sorry

/-- Difference of isomorphism classes, as an Ext¹ class. Subtraction is oriented
so that `[O'_ξ] -ᵥ [O'] = ξ` when `o(O', O'_ξ) = ξ`. -/
def vsub (p q : IsoClass π hπ fSharp G c) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  Quotient.lift₂ (fun S₁ S₂ ↦ obstruction S₂ S₁) sorry p q


/-- The transported obstruction is the certified common-presentation difference class. -/
theorem obstruction_eq_extClassOf (S T : Solution π hπ fSharp G c)
    (cert : Difference.Certificates S T) :
    obstruction S T = Difference.extClassOf S T cert := sorry

/-- A graph-quotient translation realizes the extension class of its representative. -/
theorem isTranslation_obstruction
    {ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G))}
    {S T : Solution π hπ fSharp G c} (h : IsTranslation ξ S T) :
    obstruction S T = ξ := sorry

/-- Translations of isomorphic solutions by the same class remain isomorphic. -/
theorem isTranslation_respects_iso
    {ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G))}
    {S S' T T' : Solution π hπ fSharp G c}
    (hSS' : isoSetoid π hπ fSharp G c S S')
    (hST : IsTranslation ξ S T) (hST' : IsTranslation ξ S' T') :
    isoSetoid π hπ fSharp G c T T' := sorry

/-- A translation by the zero extension class fixes the isomorphism class. -/
theorem isTranslation_zero {S T : Solution π hπ fSharp G c}
    (h : IsTranslation 0 S T) : isoClassMk T = isoClassMk S := sorry

/-- Successive translations agree with translation by the sum on isomorphism classes. -/
theorem isTranslation_add
    {ξ η : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G))}
    {S T U V : Solution π hπ fSharp G c}
    (hST : IsTranslation ξ S T) (hTU : IsTranslation η T U)
    (hSV : IsTranslation (ξ + η) S V) : isoClassMk U = isoClassMk V := sorry

/-- Translation by the obstruction between two solutions recovers the target class. -/
theorem isTranslation_obstruction_cancel {S T U : Solution π hπ fSharp G c}
    (h : IsTranslation (obstruction S T) S U) :
    isoClassMk U = isoClassMk T := sorry

variable (d : ∀ ξ : Ext⁽(1 : ℤ)⁾(
  DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
  DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)),
  TranslationData (π := π) (hπ := hπ) (c := c) ξ)
variable (cert : ∀ S T : Solution π hπ fSharp G c, Difference.Certificates S T)

/-- Translation on isomorphism classes from supplied conormal representatives. -/
def vaddOf
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)))
    (p : IsoClass π hπ fSharp G c) : IsoClass π hπ fSharp G c :=
  Quotient.map (translateWith (d ξ)) sorry p

/-- Subtraction on isomorphism classes from certified common-presentation differences. -/
def vsubOf (p q : IsoClass π hπ fSharp G c) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  Quotient.lift₂ (fun S T ↦ Difference.extClassOf T S (cert T S)) sorry p q

/-- The additive action on extension classes induced by supplied representatives. -/
@[reducible] def addActionOf :
    AddAction (Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)))
      (IsoClass π hπ fSharp G c) where
  vadd := vaddOf d
  zero_vadd := sorry
  add_vadd := sorry

/-- A chosen solution gives a torsor for the certified translation action and difference. -/
@[reducible] def addTorsorOf (S0 : Solution π hπ fSharp G c) :
    AddTorsor (Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)))
      (IsoClass π hπ fSharp G c) where
  toAddAction := addActionOf d
  vsub := vsubOf cert
  nonempty := ⟨isoClassMk S0⟩
  vsub_vadd' := sorry
  vadd_vsub' := sorry

/-- With representatives and specified-map certificates, translation of a chosen solution
identifies extension classes with the isomorphism classes of solutions. -/
def isoClassEquivOf (S0 : Solution π hπ fSharp G c) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)) ≃
      IsoClass π hπ fSharp G c where
  toFun ξ := vaddOf d ξ (isoClassMk S0)
  invFun p := vsubOf cert p (isoClassMk S0)
  left_inv := sorry
  right_inv := sorry

/-- The based equivalence sends an extension class to translation of the basepoint. -/
theorem isoClassEquivOf_apply (S0 : Solution π hπ fSharp G c)
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G))) :
    isoClassEquivOf d cert S0 ξ = vaddOf d ξ (isoClassMk S0) := sorry

/-- The based equivalence sends zero to the chosen solution class. -/
theorem isoClassEquivOf_zero (S0 : Solution π hπ fSharp G c) :
    isoClassEquivOf d cert S0 0 = isoClassMk S0 := sorry

/-- The inverse based equivalence is the certified difference from the basepoint. -/
theorem isoClassEquivOf_symm_apply (S0 : Solution π hπ fSharp G c)
    (p : IsoClass π hπ fSharp G c) :
    (isoClassEquivOf d cert S0).symm p = vsubOf cert p (isoClassMk S0) := sorry

end Solution
end FirstOrderThickening
end SheafOfModules.RingedSite
