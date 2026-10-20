/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap91.Lemma_91_13_1_Obstruction

public import Mathlib.Algebra.Torsor.Defs
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Left
public import stacks_project.Chap91.Lemma_91_13_3_Translate

/-!
# Isomorphism classes of solutions of a first-order ringed-topos equation

Two solutions of 91.13.0.1 are isomorphic when a fitting map exists for the
identity cube. Their classes form a principal homogeneous space under
Ext⁽1⁾(Q NL(fSharp), Q(𝒢[0])), via pushout translation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.NaiveCotangent
open scoped DerivedExt SheafOfModules.RingedSite

noncomputable section

universe u

namespace CategoryTheory.Functor

/-- The functor on homotopy categories induced by the identity functor is canonically
isomorphic to the identity functor. -/
def mapHomotopyCategoryIdIso (A : Type u) [Category A] [Preadditive A] :
    (𝟭 A).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      𝟭 (HomotopyCategory A (ComplexShape.up ℤ)) :=
  CategoryTheory.Quotient.natIsoLift _
    (Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ))
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)))

end CategoryTheory.Functor

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SameSite.pullbackDerived

/-- Same-site module pullback along the identity is canonically the identity functor. -/
def pullbackIdIso (O : Sheaf J CommRingCat.{u}) :
    (sameSiteHom (𝟙 O)).modulePullback ≅ 𝟭 (ringedSiteModuleCategory.{u, u, u, u} J O) :=
  pullbackExtendIso (𝟙 O) ≪≫ extendIdIso O

/-- The homotopy-level identity-pullback model is canonically isomorphic to the
derived localization functor. -/
def idSourceIso (O : Sheaf J CommRingCat.{u}) :
    RingedSite.Hom.modulePullbackToDerived (sameSiteHom (𝟙 O)) ≅
      RingedSite.Hom.moduleLocalization (RingedSite.ofCommRingSheaf J O) :=
  Functor.isoWhiskerRight
      ((Functor.mapHomotopyCategoryIso (pullbackIdIso O)) ≪≫
        Functor.mapHomotopyCategoryIdIso (ringedSiteModuleCategory.{u, u, u, u} J O))
      (RingedSite.Hom.moduleLocalization (RingedSite.ofCommRingSheaf J O)) ≪≫
    Functor.leftUnitor _

/-- The canonical counit presenting the identity of the derived category as a left-derived
model of pullback along `𝟙 O`. -/
def idCounit (O : Sheaf J CommRingCat.{u}) :
    RingedSite.Hom.moduleLocalization (RingedSite.ofCommRingSheaf J O) ⋙
        𝟭 (RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J O)) ⟶
      RingedSite.Hom.modulePullbackToDerived (sameSiteHom (𝟙 O)) :=
  (Functor.rightUnitor _).hom ≫ (idSourceIso O).inv

/-- The identity functor with `idCounit` has the canonical left-derived universal property. -/
instance idFunctorIsLeftDerived (O : Sheaf J CommRingCat.{u}) :
    (𝟭 (RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J O))).IsLeftDerivedFunctor
      (idCounit O) (RingedSite.Hom.ModuleQis (RingedSite.ofCommRingSheaf J O)) := sorry

/-- Derived pullback along the identity is canonically isomorphic to the identity functor. -/
def idIso (O : Sheaf J CommRingCat.{u}) :
    SameSite.pullbackDerived.{u, u, u, u} (𝟙 O) ≅
      𝟭 (RingedSite.Hom.ModuleDerived.{u} (RingedSite.ofCommRingSheaf J O)) :=
  Functor.leftDerivedNatIso
    (SameSite.pullbackDerived.{u, u, u, u} (𝟙 O))
    (𝟭 (RingedSite.Hom.ModuleDerived.{u} (RingedSite.ofCommRingSheaf J O)))
    ((RingedSite.Hom.modulePullbackToDerived.{u} (sameSiteHom (𝟙 O))).totalLeftDerivedCounit
      (RingedSite.Hom.moduleLocalization (RingedSite.ofCommRingSheaf J O))
      (RingedSite.Hom.ModuleQis.{u} (RingedSite.ofCommRingSheaf J O)))
    (idCounit O) (RingedSite.Hom.ModuleQis.{u} (RingedSite.ofCommRingSheaf J O)) (Iso.refl _)

/-- `idIso` identifies derived pullback along `𝟙 O` with the identity functor. -/
theorem idIso_hom_app (O : Sheaf J CommRingCat.{u})
    (K : RingedSite.Hom.ModuleDerived.{u} (RingedSite.ofCommRingSheaf J O)) :
    (idIso O).hom.app K =
      (Functor.leftDerivedNatIso
        (SameSite.pullbackDerived.{u, u, u, u} (𝟙 O))
        (𝟭 (RingedSite.Hom.ModuleDerived.{u} (RingedSite.ofCommRingSheaf J O)))
        ((RingedSite.Hom.modulePullbackToDerived.{u} (sameSiteHom (𝟙 O))).totalLeftDerivedCounit
          (RingedSite.Hom.moduleLocalization (RingedSite.ofCommRingSheaf J O))
          (RingedSite.Hom.ModuleQis.{u} (RingedSite.ofCommRingSheaf J O)))
        (idCounit O) (RingedSite.Hom.ModuleQis.{u} (RingedSite.ofCommRingSheaf J O))
        (Iso.refl _)).hom.app K := sorry

end SameSite.pullbackDerived

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
instance instIsFirstOrderThickening_sol (sol : Solution π hπ fSharp G c) :
    IsFirstOrderThickening sol.proj where
  isLocallySurjective := sol.proj_locallySurjective
  isSquareZero := sol.proj_squareZero

/-- The first-order kernel module of `sol.proj` agrees with the stored square-zero target
module of `sol`. -/
def idealTargetIso (sol : Solution π hπ fSharp G c) :
    ideal sol.proj ≅ sol.proj_squareZero.targetModule sol.proj_quotient_isIso where
  hom :=
    ⟨PresheafOfModules.homMk
      ((sheafToPresheaf J AddCommGrpCat.{u}).map
        ((sol.proj_squareZero.targetModuleForgetIso
            (KernelIdeal.quotientComparison_isIso sol.proj)).hom ≫
          (sol.proj_squareZero.targetModuleForgetIso sol.proj_quotient_isIso).inv))
      (fun _ _ _ ↦ sorry)⟩
  inv :=
    ⟨PresheafOfModules.homMk
      ((sheafToPresheaf J AddCommGrpCat.{u}).map
        ((sol.proj_squareZero.targetModuleForgetIso sol.proj_quotient_isIso).hom ≫
          (sol.proj_squareZero.targetModuleForgetIso
            (KernelIdeal.quotientComparison_isIso sol.proj)).inv))
      (fun _ _ _ ↦ sorry)⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underlying additive map of `idealTargetIso` is the composite of the two
`targetModuleForgetIso`s. -/
theorem idealTargetIso_toSheaf (sol : Solution π hπ fSharp G c) :
    (SheafOfModules.toSheaf (ringSheaf J O)).map (idealTargetIso sol).hom =
      (sol.proj_squareZero.targetModuleForgetIso
          (KernelIdeal.quotientComparison_isIso sol.proj)).hom ≫
        (sol.proj_squareZero.targetModuleForgetIso sol.proj_quotient_isIso).inv := sorry

/-- Kernel identification of a solution, as a map `ideal sol.proj ⟶ 𝒢`. -/
def kernelIdealHom (sol : Solution π hπ fSharp G c) :
    ideal sol.proj ⟶ G :=
  (idealTargetIso sol).hom ≫ sol.kernelIso.hom

/-- `kernelIdealHom` is `idealTargetIso` followed by `kernelIso`. -/
theorem kernelIdealHom_spec (sol : Solution π hπ fSharp G c) :
    kernelIdealHom sol = (idealTargetIso sol).hom ≫ sol.kernelIso.hom := sorry

/-- The identity connecting cube comparing two solutions of the same equation, with
front face `S₁`, back face `S₂`, and `g = 𝟙 O`. -/
-- Local instance justification (noncanonical choice): `hπ` is the explicit square-zero
-- witness of the 91.13.0.1 equation, not a globally unique first-order structure on `π`.
def compare (S₁ S₂ : Solution π hπ fSharp G c) :
    letI := instIsFirstOrderThickening_π (hπ := hπ)
    RelativeDiagram S₁.proj π S₂.proj π :=
  letI := instIsFirstOrderThickening_π (hπ := hπ)
  RelativeDiagram.of fSharp S₁.structureMap S₁.commutes fSharp S₂.structureMap S₂.commutes
    (𝟙 O) (𝟙 O_B) (𝟙 O_B')
    ((Category.id_comp π).trans (Category.comp_id π).symm)
    ((Category.id_comp fSharp).trans (Category.comp_id fSharp).symm)
    ((idealTargetIso S₁).hom ≫ S₁.kernelIso.hom ≫ S₂.kernelIso.inv ≫
      (idealTargetIso S₂).inv ≫
        (SheafOfModules.Restriction.idIso' (ringSheafMap (𝟙 O))
          (ringSheafMap_id O)).hom.app (ideal S₂.proj))
    sorry

/-- The identity connecting cube has identity maps on `O`, `O_B`, and `O_{B'}`, and `ν` is
the identity-restriction composite of the two kernel identifications. -/
theorem compare_spec (S₁ S₂ : Solution π hπ fSharp G c) :
    letI := instIsFirstOrderThickening_π (hπ := hπ)
    (compare S₁ S₂).f1 = fSharp ∧ (compare S₁ S₂).f2 = fSharp ∧
      (compare S₁ S₂).f1' = S₁.structureMap ∧
      (compare S₁ S₂).f2' = S₂.structureMap ∧
      (compare S₁ S₂).g = 𝟙 O ∧ (compare S₁ S₂).t = 𝟙 O_B ∧
      (compare S₁ S₂).t' = 𝟙 O_B' ∧
      (compare S₁ S₂).ν =
        (idealTargetIso S₁).hom ≫ S₁.kernelIso.hom ≫ S₂.kernelIso.inv ≫
          (idealTargetIso S₂).inv ≫
            (SheafOfModules.Restriction.idIso' (ringSheafMap (𝟙 O))
              (ringSheafMap_id O)).hom.app (ideal S₂.proj) := sorry

/-- The setoid identifying solutions that admit a fitting map of `compare`. -/
def isoSetoid (π : O_B' ⟶ O_B) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π) (fSharp : O_B ⟶ O)
    (G : SheafOfModules (ringSheaf J O))
    (c : hπ.targetModule (KernelIdeal.quotientComparison_isIso π) ⟶
      (restrictionAlong fSharp).obj G) :
    Setoid (Solution π hπ fSharp G c) where
  r S₁ S₂ :=
    letI := instIsFirstOrderThickening_π (hπ := hπ)
    Nonempty (FittingMap (compare S₁ S₂))
  iseqv := sorry

/-- Two solutions are related iff the identity cube admits a fitting map. -/
theorem isoSetoid_rel (S₁ S₂ : Solution π hπ fSharp G c) :
    letI := instIsFirstOrderThickening_π (hπ := hπ)
    isoSetoid π hπ fSharp G c S₁ S₂ ↔ Nonempty (FittingMap (compare S₁ S₂)) := sorry

/-- Isomorphism classes of solutions of a fixed diagram 91.13.0.1. -/
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
    (φ : letI := instIsFirstOrderThickening_π (hπ := hπ); FittingMap (compare S₁ S₂)) :
    isoClassMk S₁ = isoClassMk S₂ := sorry

/-- The obstruction class o(O'₁, O'₂) in Ext⁽1⁾(Q NL(fSharp), Q(𝒢[0])), obtained by
transporting `mapObstruction` of the identity cube along L(𝟙 O)^* ≅ id and the
back kernel identification. -/
def obstruction (S₁ S₂ : Solution π hπ fSharp G c) :
    Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  letI := instIsFirstOrderThickening_π (hπ := hπ)
  (SameSite.pullbackDerived.idIso O).inv.app
      ((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp))) ≫
    mapObstruction (compare S₁ S₂) ≫
      (shiftFunctor (DerivedCategory (ringedSiteModuleCategory.{u, u, u, u} J O)) (1 : ℤ)).map
        ((moduleQ O).map
          ((CochainComplex.singleFunctor
              (ringedSiteModuleCategory.{u, u, u, u} J O) 0).map
            (kernelIdealHom S₂)))

/-- `obstruction` is `mapObstruction` of `compare`, transported to
Ext⁽1⁾(Q NL(fSharp), Q(𝒢[0])). -/
theorem obstruction_spec (S₁ S₂ : Solution π hπ fSharp G c) :
    letI := instIsFirstOrderThickening_π (hπ := hπ)
    obstruction S₁ S₂ =
      (SameSite.pullbackDerived.idIso O).inv.app
          ((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp))) ≫
        mapObstruction (compare S₁ S₂) ≫
          (shiftFunctor
              (DerivedCategory (ringedSiteModuleCategory.{u, u, u, u} J O)) (1 : ℤ)).map
            ((moduleQ O).map
              ((CochainComplex.singleFunctor
                  (ringedSiteModuleCategory.{u, u, u, u} J O) 0).map
                (kernelIdealHom S₂))) := sorry

/-- The obstruction vanishes if and only if the identity cube admits a fitting map. -/
theorem obstruction_eq_zero_iff (S₁ S₂ : Solution π hπ fSharp G c) :
    letI := instIsFirstOrderThickening_π (hπ := hπ)
    obstruction S₁ S₂ = 0 ↔ Nonempty (FittingMap (compare S₁ S₂)) := sorry

/-- Translating a solution by ξ realizes ξ as an obstruction. -/
theorem obstruction_translate
    (ξ : Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G)))
    (sol : Solution π hπ fSharp G c) :
    letI := instIsFirstOrderThickening_π (hπ := hπ)
    obstruction sol (translate ξ sol) = ξ := sorry

/-- Action of an Ext¹ class on an isomorphism class, via `translate`. -/
def vadd
    (ξ : Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G)))
    (p : IsoClass π hπ fSharp G c) : IsoClass π hπ fSharp G c :=
  Quotient.map (translate ξ) sorry p

/-- Difference of isomorphism classes, as an Ext¹ class. Subtraction is oriented
so that `[O'_ξ] -ᵥ [O'] = ξ` when `o(O', O'_ξ) = ξ`. -/
def vsub (p q : IsoClass π hπ fSharp G c) :
    Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  Quotient.lift₂ (fun S₁ S₂ ↦ obstruction S₂ S₁) sorry p q

/-- Ext¹ classes act on isomorphism classes of solutions by translation. -/
instance instVAdd_isoClass :
    VAdd (Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G)))
      (IsoClass π hπ fSharp G c) where
  vadd := vadd

/-- Difference of isomorphism classes of solutions is an Ext¹ class. -/
instance instVSub_isoClass :
    VSub (Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G)))
      (IsoClass π hπ fSharp G c) where
  vsub := vsub

/-- The Ext¹-action of naive cotangent classes on isomorphism classes of solutions. -/
instance instAddAction_isoClass :
    AddAction (Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G)))
      (IsoClass π hπ fSharp G c) where
  add_vadd := sorry
  zero_vadd := sorry

/-- The Ext¹-action computes on representatives by `translate`. -/
theorem vadd_mk
    (ξ : Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G)))
    (sol : Solution π hπ fSharp G c) :
    ξ +ᵥ isoClassMk sol = isoClassMk (translate ξ sol) := sorry

/-- Torsor subtraction computes on representatives by the reversed obstruction. -/
theorem vsub_mk (S₁ S₂ : Solution π hπ fSharp G c) :
    isoClassMk S₁ -ᵥ isoClassMk S₂ = obstruction S₂ S₁ := sorry

/-- The zero Ext¹ class acts as the identity on isomorphism classes. -/
theorem vadd_zero (p : IsoClass π hπ fSharp G c) :
    (0 : Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G))) +ᵥ p = p := sorry

/-- The Ext¹-action is compatible with addition. -/
theorem add_vadd
    (ξ η : Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G)))
    (p : IsoClass π hπ fSharp G c) :
    (ξ + η) +ᵥ p = ξ +ᵥ η +ᵥ p := sorry

/-- With a chosen solution as basepoint, isomorphism classes are an additive torsor
under Ext⁽1⁾(Q NL(fSharp), Q(𝒢[0])). -/
@[reducible]
def addTorsor (S0 : Solution π hπ fSharp G c) :
    AddTorsor (Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G)))
      (IsoClass π hπ fSharp G c) where
  nonempty := ⟨isoClassMk S0⟩
  vsub_vadd' := sorry
  vadd_vsub' := sorry

/-- A basepoint solution makes the set of isomorphism classes nonempty. -/
theorem addTorsor_nonempty (S0 : Solution π hπ fSharp G c) :
    Nonempty (IsoClass π hπ fSharp G c) := (addTorsor S0).nonempty

end Solution
end FirstOrderThickening
end SheafOfModules.RingedSite
