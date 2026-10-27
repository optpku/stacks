/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ModuleExtension.IsoClass
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.FlatLift

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.ChangeOfRings
open SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.FirstOrderThickening
namespace FlatLift

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable {OB' O' O : Sheaf J CommRingCat.{max u v}}
variable (π : O' ⟶ O)
variable [hπ : IsFirstOrderThickening π]
variable [(restrictScalars (ringSheafMap π)).IsRightAdjoint]
variable (f' : OB' ⟶ O')
variable (F : ringedSiteModuleCategory.{u, v, max u v, max u v} J O)

/-- Isomorphism of flat lifts is an equivalence relation. -/
theorem isomorphicSetoid_iseqv :
    Equivalence (fun L₁ L₂ : FlatLift π f' F ↦ Nonempty (FlatLift.Hom L₁ L₂)) := sorry

/-- Two flat lifts are equivalent when there is an isomorphism of pairs. -/
def isomorphicSetoid : Setoid (FlatLift π f' F) where
  r L₁ L₂ := Nonempty (FlatLift.Hom L₁ L₂)
  iseqv := isomorphicSetoid_iseqv π f' F

/-- Isomorphism classes of flat lifts of `F` along `π`. -/
abbrev IsoClass := Quotient (isomorphicSetoid π f' F)

namespace IsoClass

/-- The isomorphism class of a given flat lift. -/
def mk (L : FlatLift π f' F) : IsoClass π f' F :=
  Quotient.mk (isomorphicSetoid π f' F) L

end IsoClass

variable {π f' F}
variable {OB : Sheaf J CommRingCat.{max u v}} {τ : OB' ⟶ OB}
variable [IsFirstOrderThickening τ]
variable {f : OB ⟶ O} [(restrictScalars (ringSheafMap f)).IsRightAdjoint]
variable {hcomm : f' ≫ π = τ ≫ f}

/-- Translate a flat lift by the restriction of an `O`-module extension, using the
Baer sum on the associated extension with `c = 𝟙`. The result remains a flat
lift because `(f, f')` is strict and `F` is flat over `O_B`. -/
def vaddLift [IsFlat OB ((restrictionAlong f).obj F)]
    (hstrict : IsStrict f f' hcomm)
    (ξ : CategoryTheory.Extension (moduleTensor (ideal π) F) F)
    (L : FlatLift π f' F) : FlatLift π f' F :=
  ofModuleExtension f' hstrict ⟨L⟩
    (ModuleExtension.vaddExtension ξ (toModuleExtension f' hstrict L))

/-- Baer-sum translation preserves isomorphism of flat lifts. -/
theorem vaddLift_isomorphic [IsFlat OB ((restrictionAlong f).obj F)]
    (hstrict : IsStrict f f' hcomm)
    {ξ ξ' : CategoryTheory.Extension (moduleTensor (ideal π) F) F}
    (hξ : IsIsomorphic ξ ξ') {L L' : FlatLift π f' F}
    (hL : Nonempty (FlatLift.Hom L L')) :
    Nonempty (FlatLift.Hom (vaddLift hstrict ξ L) (vaddLift hstrict ξ' L')) := sorry

/-- The Baer-sum action of `O`-module extension classes on isomorphism classes of
flat lifts, along a strict morphism with `F` flat over `O_B`. -/
def vadd [IsFlat OB ((restrictionAlong f).obj F)]
    (hstrict : IsStrict f f' hcomm)
    (ξ : ExtensionClass (moduleTensor (ideal π) F) F) (E : IsoClass π f' F) :
    IsoClass π f' F :=
  Quotient.map₂ (vaddLift hstrict)
    (fun _ _ hξ _ _ hL ↦ vaddLift_isomorphic hstrict hξ hL) ξ E

/-- The Baer-sum action computes on representatives. -/
theorem vadd_mk [IsFlat OB ((restrictionAlong f).obj F)]
    (hstrict : IsStrict f f' hcomm)
    (ξ : CategoryTheory.Extension (moduleTensor (ideal π) F) F)
    (L : FlatLift π f' F) :
    vadd hstrict (Quotient.mk (isIsomorphicSetoid
          (CategoryTheory.Extension (moduleTensor (ideal π) F) F)) ξ)
      (Quotient.mk (isomorphicSetoid π f' F) L) =
      Quotient.mk (isomorphicSetoid π f' F) (vaddLift hstrict ξ L) := sorry

/-- The split `O`-module extension acts trivially on isomorphism classes. -/
theorem vadd_zero [IsFlat OB ((restrictionAlong f).obj F)]
    (hstrict : IsStrict f f' hcomm) (E : IsoClass π f' F) :
    vadd hstrict (0 : ExtensionClass (moduleTensor (ideal π) F) F) E = E := sorry

/-- The Baer-sum action is an action of the extension group. -/
theorem vadd_add [IsFlat OB ((restrictionAlong f).obj F)]
    (hstrict : IsStrict f f' hcomm)
    (ξ η : ExtensionClass (moduleTensor (ideal π) F) F)
    (E : IsoClass π f' F) :
    vadd hstrict (ξ + η) E = vadd hstrict ξ (vadd hstrict η E) := sorry

/-- If at least one flat lift exists, then along a strict morphism with `F` flat
over `O_B`, isomorphism classes form a principal homogeneous space under the
`O`-module extension group of `F` by `I ⊗_O F`. -/
theorem existsUnique_vadd [IsFlat OB ((restrictionAlong f).obj F)]
    (hstrict : IsStrict f f' hcomm) (h_exists : Nonempty (FlatLift π f' F))
    (E E' : IsoClass π f' F) :
    ∃! ξ : ExtensionClass (moduleTensor (ideal π) F) F,
      vadd hstrict ξ E = E' := sorry

variable [HasExt.{w} (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)]

/-- The Baer-sum action on isomorphism classes depends only on the Ext¹ class of the
acting `O`-module extension. -/
theorem vadd_congr_toExt [IsFlat OB ((restrictionAlong f).obj F)]
    (hstrict : IsStrict f f' hcomm)
    {ξ η : ExtensionClass (moduleTensor (ideal π) F) F}
    (h : ExtensionClass.toExt ξ = ExtensionClass.toExt η) (E : IsoClass π f' F) :
    vadd hstrict ξ E = vadd hstrict η E := sorry

end FlatLift
end SheafOfModules.RingedSite.FirstOrderThickening
