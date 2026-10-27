/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.IsoClass
public import stacks_project.Chap91.Lemma_91_13_1_Obstruction
public import stacks_project.Chap91.Lemma_91_13_3_Translate

/-! Legacy quotient-action interface for the fixed first-order deformation diagram. -/

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

/-- The selected conormal representative gives an actual graph-quotient translation. -/
private theorem translate_isTranslation
    (ξ : Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G)))
    (sol : Solution π hπ fSharp G c) : IsTranslation ξ sol (translate ξ sol) := by
  obtain ⟨E, α, hs, δ, hrep, htranslate⟩ := translate_spec ξ sol
  -- Local instance justification (proof-local temporary data): the comparison and kernel-inclusion theorems consume the supplied local-surjectivity proof of this exact representative evaluation through class arguments.
  letI := hs
  refine ⟨
    { E := E
      α := α
      evaluation := hs
      δ := δ
      hq := Presentation.toCanonicalMap_quasiIso E α
      represents := hrep
      kernelIsIso := fun S ↦ translateKernelInclusion_isIso E α δ S }, ?_⟩
  exact htranslate

/-- Translating a solution by ξ realizes ξ as an obstruction. -/
theorem obstruction_translate
    (ξ : Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G)))
    (sol : Solution π hπ fSharp G c) :
    obstruction sol (translate ξ sol) = ξ :=
  isTranslation_obstruction (translate_isTranslation ξ sol)

/-- Action of an Ext¹ class on an isomorphism class, via `translate`. -/
@[no_expose] def vadd
    (ξ : Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G)))
    (p : IsoClass π hπ fSharp G c) : IsoClass π hπ fSharp G c :=
  Quotient.map (translate ξ) (fun S T h ↦
    isTranslation_respects_iso h (translate_isTranslation ξ S)
      (translate_isTranslation ξ T)) p

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
  vadd := vadd
  add_vadd ξ η p := by
    refine Quotient.inductionOn p fun S ↦ ?_
    exact (add_comm ξ η ▸ isTranslation_add
      (translate_isTranslation η S) (translate_isTranslation ξ (translate η S))
      (translate_isTranslation (η + ξ) S)).symm
  zero_vadd p := by
    refine Quotient.inductionOn p fun S ↦ ?_
    exact isTranslation_zero (translate_isTranslation 0 S)

/-- The Ext¹-action computes on representatives by `translate`. -/
theorem vadd_mk
    (ξ : Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G)))
    (sol : Solution π hπ fSharp G c) :
    ξ +ᵥ isoClassMk sol = isoClassMk (translate ξ sol) := by
  rfl

/-- Torsor subtraction computes on representatives by the reversed obstruction. -/
theorem vsub_mk (S₁ S₂ : Solution π hπ fSharp G c) :
    isoClassMk S₁ -ᵥ isoClassMk S₂ = obstruction S₂ S₁ := rfl

/-- The zero Ext¹ class acts as the identity on isomorphism classes. -/
theorem vadd_zero (p : IsoClass π hπ fSharp G c) :
    (0 : Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G))) +ᵥ p = p :=
  instAddAction_isoClass.zero_vadd p

/-- The Ext¹-action is compatible with addition. -/
theorem add_vadd
    (ξ η : Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G)))
    (p : IsoClass π hπ fSharp G c) :
    (ξ + η) +ᵥ p = ξ +ᵥ η +ᵥ p :=
  instAddAction_isoClass.toAddSemigroupAction.add_vadd ξ η p

/-- With a chosen solution as basepoint, isomorphism classes are an additive torsor
under Ext⁽1⁾(Q NL(fSharp), Q(𝒢[0])). -/
@[reducible]
def addTorsor (S0 : Solution π hπ fSharp G c) :
    AddTorsor (Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G)))
      (IsoClass π hπ fSharp G c) where
  toAddAction := instAddAction_isoClass
  vsub := vsub
  nonempty := ⟨isoClassMk S0⟩
  vsub_vadd' p q := by
    refine Quotient.inductionOn₂ p q fun S T ↦ ?_
    exact isTranslation_obstruction_cancel (translate_isTranslation (obstruction T S) T)
  vadd_vsub' ξ p := by
    refine Quotient.inductionOn p fun S ↦ ?_
    exact isTranslation_obstruction (translate_isTranslation ξ S)

/-- A basepoint solution makes the set of isomorphism classes nonempty. -/
theorem addTorsor_nonempty (S0 : Solution π hπ fSharp G c) :
    Nonempty (IsoClass π hπ fSharp G c) := (addTorsor S0).nonempty

end Solution
end FirstOrderThickening
end SheafOfModules.RingedSite
