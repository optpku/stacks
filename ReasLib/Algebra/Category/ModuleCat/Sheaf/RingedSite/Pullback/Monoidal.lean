/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Pullback.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Monoidal pullback for sheaves of modules

For a continuous functor of sites, this file transports an explicitly supplied strong-monoidal
core for presheaf pullback through module sheafification and the monoidal localization. It also
provides the canonical core arising from representable flatness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u uC vC uD vD

namespace SheafOfModules.Pullback

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify K AddCommGrpCat.{u}]
variable [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (F : C ⥤ D) [F.IsContinuous J K]
variable {O : Sheaf J CommRingCat.{u}} {O' : Sheaf K CommRingCat.{u}}
variable (b : O ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj O')

/-- The underlying morphism of ring sheaves defining module pullback. -/
@[stacks 03EL "underlying ring map"]
abbrev ringMap :
    CategoryTheory.Sheaf.ringSheafOfComm O ⟶
      (F.sheafPushforwardContinuous RingCat.{u} J K).obj
        (CategoryTheory.Sheaf.ringSheafOfComm O') :=
  CategoryTheory.Sheaf.ringSheafOfCommMap b

variable [pullbackExists :
  (PresheafOfModules.pushforward.{u} (ringMap F b).hom).IsRightAdjoint]

/-- The explicit presheaf strong-monoidal core consumed by sheaf pullback.

Naming this type at the ringed-site layer keeps geometric specializations from repeating the
underlying presheaf-pullback presentation. -/
@[stacks 03EL "presheaf core for sheaf pullback"]
abbrev presheafCore :=
  (PresheafOfModules.pullback.{u} (ringMap F b).hom).CoreMonoidal

namespace Construction

/-- The presheaf pushforward adjoint instance in the commutative-ring presentation of `b.hom`. -/
@[stacks 03EL "presheaf pushforward adjoint bridge"]
noncomputable instance pushforwardAdjoint :
    (PresheafOfModules.pushforward.{u}
      (PresheafOfModules.Pullback.ringMap F b.hom)).IsRightAdjoint :=
  inferInstanceAs
    ((PresheafOfModules.pushforward.{u} (ringMap F b).hom).IsRightAdjoint)

/-- Compose an explicitly supplied presheaf monoidal core with module sheafification.

The argument is a `CoreMonoidal` value rather than a typeclass so that the inverse data used by
the composite is visible at the API boundary. -/
@[stacks 03EL "explicit monoidal presheaf model", implicit_reducible]
noncomputable def compositeMonoidalOf
    (m : presheafCore F b) :
    (PresheafOfModules.pullback.{u} (ringMap F b).hom ⋙
      PresheafOfModules.sheafification
        (R₀ := (CategoryTheory.Sheaf.ringSheafOfComm O').obj)
        (R := CategoryTheory.Sheaf.ringSheafOfComm O')
        (𝟙 (CategoryTheory.Sheaf.ringSheafOfComm O').obj)).Monoidal :=
  @Functor.Monoidal.instComp _ _ _ _ _ _ _ _ _
    (PresheafOfModules.pullback.{u} (ringMap F b).hom)
    (PresheafOfModules.sheafification
      (R₀ := (CategoryTheory.Sheaf.ringSheafOfComm O').obj)
      (R := CategoryTheory.Sheaf.ringSheafOfComm O')
      (𝟙 (CategoryTheory.Sheaf.ringSheafOfComm O').obj))
    m.toMonoidal
    (SheafOfModules.RingedSite.Tensor.sheafificationMonoidal O')

/-- The comparison identifying sheaf pullback with its sheafified presheaf model. -/
@[stacks 03EL "pullback localization lifting"]
noncomputable instance lifting :
    Localization.Lifting
      (PresheafOfModules.sheafification
        (R₀ := (CategoryTheory.Sheaf.ringSheafOfComm O).obj)
        (R := CategoryTheory.Sheaf.ringSheafOfComm O)
        (𝟙 (CategoryTheory.Sheaf.ringSheafOfComm O).obj))
      (SheafOfModules.RingedSite.Tensor.weakEquivalences O)
      (PresheafOfModules.pullback.{u} (ringMap F b).hom ⋙
        PresheafOfModules.sheafification
          (R₀ := (CategoryTheory.Sheaf.ringSheafOfComm O').obj)
          (R := CategoryTheory.Sheaf.ringSheafOfComm O')
          (𝟙 (CategoryTheory.Sheaf.ringSheafOfComm O').obj))
      (SheafOfModules.pullback.{u} (ringMap F b)) where
  iso := SheafOfModules.sheafificationCompPullback.{u} (ringMap F b)

section Compatibility

variable [RepresentablyFlat F]

/-- The presheaf monoidal core obtained from representable flatness. -/
@[stacks 03EL "representably flat presheaf monoidal core"]
noncomputable def presheafCoreMonoidal :
    presheafCore F b :=
  PresheafOfModules.Pullback.pullbackCoreMonoidalOf F b.hom
    (PresheafOfModules.Pullback.pullbackUnitComparison_isIso F b.hom)
    (fun M N ↦ PresheafOfModules.Pullback.pullbackTensorComparison_isIso F b.hom M N)

/-- The strong-monoidal structure on representably flat presheaf pullback. -/
@[stacks 03EL "representably flat presheaf monoidal structure", implicit_reducible]
noncomputable instance presheafMonoidal :
    (PresheafOfModules.pullback.{u} (ringMap F b).hom).Monoidal :=
  (presheafCoreMonoidal F b).toMonoidal

/-- The strong-monoidal structure on the sheafified presheaf pullback model. -/
@[stacks 03EL "representably flat monoidal presheaf model", implicit_reducible]
noncomputable instance compositeMonoidal :
    (PresheafOfModules.pullback.{u} (ringMap F b).hom ⋙
      PresheafOfModules.sheafification
        (R₀ := (CategoryTheory.Sheaf.ringSheafOfComm O').obj)
        (R := CategoryTheory.Sheaf.ringSheafOfComm O')
        (𝟙 (CategoryTheory.Sheaf.ringSheafOfComm O').obj)).Monoidal :=
  compositeMonoidalOf F b (presheafCoreMonoidal F b)

end Compatibility

end Construction

/-- Descend an explicitly supplied presheaf pullback core through module sheafification. -/
@[stacks 03EL "explicit sheaf pullback monoidal core"]
noncomputable def coreMonoidalOf
    (m : presheafCore F b) :
    (SheafOfModules.pullback.{u} (ringMap F b)).CoreMonoidal :=
  -- `Localization.Monoidal.functorCoreMonoidalOfComp` consumes the class-shaped composite;
  -- this is only the bridge from the explicit `m` datum, not a reconstructed ambient instance.
  -- Local instance justification (noncanonical choice): the explicit supplied presheaf core determines the composite structure consumed by localization.
  letI :
      (PresheafOfModules.pullback.{u} (ringMap F b).hom ⋙
        PresheafOfModules.sheafification
          (R₀ := (CategoryTheory.Sheaf.ringSheafOfComm O').obj)
          (R := CategoryTheory.Sheaf.ringSheafOfComm O')
          (𝟙 (CategoryTheory.Sheaf.ringSheafOfComm O').obj)).Monoidal :=
    Construction.compositeMonoidalOf F b m
  Localization.Monoidal.functorCoreMonoidalOfComp
    (L := PresheafOfModules.sheafification
      (R₀ := (CategoryTheory.Sheaf.ringSheafOfComm O).obj)
      (R := CategoryTheory.Sheaf.ringSheafOfComm O)
      (𝟙 (CategoryTheory.Sheaf.ringSheafOfComm O).obj))
    (W := SheafOfModules.RingedSite.Tensor.weakEquivalences O)
    (F := SheafOfModules.pullback.{u} (ringMap F b))
    (G := PresheafOfModules.pullback.{u} (ringMap F b).hom ⋙
      PresheafOfModules.sheafification
        (R₀ := (CategoryTheory.Sheaf.ringSheafOfComm O').obj)
        (R := CategoryTheory.Sheaf.ringSheafOfComm O')
        (𝟙 (CategoryTheory.Sheaf.ringSheafOfComm O').obj))

/-- The class-shaped strong-monoidal structure obtained from `coreMonoidalOf`. -/
@[stacks 03EL "explicit sheaf pullback monoidal structure", implicit_reducible]
noncomputable def monoidalOf
    (m : presheafCore F b) :
    (SheafOfModules.pullback.{u} (ringMap F b)).Monoidal :=
  (coreMonoidalOf F b m).toMonoidal

/-- The unit isomorphism read from an explicit sheaf pullback monoidal core. -/
@[stacks 03EL "explicit sheaf pullback unit isomorphism"]
noncomputable def unitIsoOf
    (m : presheafCore F b) :
    (SheafOfModules.pullback.{u} (ringMap F b)).obj
        (𝟙_ (SheafOfModules.{u} (CategoryTheory.Sheaf.ringSheafOfComm O))) ≅
      𝟙_ (SheafOfModules.{u} (CategoryTheory.Sheaf.ringSheafOfComm O')) :=
  (coreMonoidalOf F b m).εIso.symm

/-- The forward unit comparison read from an explicit sheaf pullback monoidal core. -/
@[stacks 03EL "explicit sheaf pullback unit comparison"]
noncomputable abbrev unitComparisonOf
    (m : presheafCore F b) :
    (SheafOfModules.pullback.{u} (ringMap F b)).obj
        (𝟙_ (SheafOfModules.{u} (CategoryTheory.Sheaf.ringSheafOfComm O))) ⟶
      𝟙_ (SheafOfModules.{u} (CategoryTheory.Sheaf.ringSheafOfComm O')) :=
  (unitIsoOf F b m).hom

/-- The natural tensor comparison read from an explicit sheaf pullback monoidal core. -/
@[stacks 03EL "explicit sheaf pullback tensor comparison"]
noncomputable def tensorNatIsoOf
    (m : presheafCore F b) :
    MonoidalCategory.tensor
        (SheafOfModules.{u} (CategoryTheory.Sheaf.ringSheafOfComm O)) ⋙
      SheafOfModules.pullback.{u} (ringMap F b) ≅
    Functor.prod (SheafOfModules.pullback.{u} (ringMap F b))
        (SheafOfModules.pullback.{u} (ringMap F b)) ⋙
      MonoidalCategory.tensor
        (SheafOfModules.{u} (CategoryTheory.Sheaf.ringSheafOfComm O')) :=
  -- Read the natural transformation from the supplied core through the class projection.
  -- Local instance justification (noncanonical choice): the explicit supplied presheaf core determines the monoidal structure whose tensor comparison is projected.
  letI : (SheafOfModules.pullback.{u} (ringMap F b)).Monoidal := monoidalOf F b m
  (Functor.Monoidal.μNatIso (SheafOfModules.pullback.{u} (ringMap F b))).symm

/-- The tensor comparison isomorphism read from an explicit sheaf pullback monoidal core. -/
@[stacks 03EL "explicit sheaf pullback tensor isomorphism"]
noncomputable def tensorIsoOf
    (m : presheafCore F b)
    (M N : SheafOfModules.{u} (CategoryTheory.Sheaf.ringSheafOfComm O)) :
    (SheafOfModules.pullback.{u} (ringMap F b)).obj (M ⊗ N) ≅
      ((SheafOfModules.pullback.{u} (ringMap F b)).obj M ⊗
        (SheafOfModules.pullback.{u} (ringMap F b)).obj N) :=
  (coreMonoidalOf F b m).μIso M N |>.symm

/- The component bridge keeps downstream statements at the object level instead of unfolding
the `Functor.Monoidal` projection each time. -/
/-- The component of `tensorNatIsoOf` is the named objectwise tensor isomorphism. -/
@[simp, stacks 03EL "tensor comparison component"]
theorem tensorNatIsoOf_app
    (m : presheafCore F b)
    (M N : SheafOfModules.{u} (CategoryTheory.Sheaf.ringSheafOfComm O)) :
    (tensorNatIsoOf F b m).app (M, N) = tensorIsoOf F b m M N := sorry

/-- The forward tensor comparison read from an explicit sheaf pullback monoidal core. -/
@[stacks 03EL "explicit sheaf pullback tensor comparison morphism"]
noncomputable abbrev tensorComparisonOf
    (m : presheafCore F b)
    (M N : SheafOfModules.{u} (CategoryTheory.Sheaf.ringSheafOfComm O)) :
    (SheafOfModules.pullback.{u} (ringMap F b)).obj (M ⊗ N) ⟶
      ((SheafOfModules.pullback.{u} (ringMap F b)).obj M ⊗
        (SheafOfModules.pullback.{u} (ringMap F b)).obj N) :=
  (tensorIsoOf F b m M N).hom

section Compatibility

variable [RepresentablyFlat F]

/-- The canonical sheaf-pullback core selected by representable flatness. -/
@[stacks 03EL "representably flat sheaf pullback core"]
noncomputable def coreMonoidal :
    (SheafOfModules.pullback.{u} (ringMap F b)).CoreMonoidal :=
  coreMonoidalOf F b (Construction.presheafCoreMonoidal F b)

/-- Representably flat pullback of module sheaves is strong monoidal. -/
@[stacks 03EL "commutative ringed-site pullback", implicit_reducible]
noncomputable instance monoidal :
    (SheafOfModules.pullback.{u} (ringMap F b)).Monoidal :=
  (coreMonoidal F b).toMonoidal

/-- The unit isomorphism for representably flat pullback of module sheaves. -/
@[stacks 03EL "unit comparison on objects"]
noncomputable abbrev unitIso :
    (SheafOfModules.pullback.{u} (ringMap F b)).obj
        (𝟙_ (SheafOfModules.{u} (CategoryTheory.Sheaf.ringSheafOfComm O))) ≅
      𝟙_ (SheafOfModules.{u} (CategoryTheory.Sheaf.ringSheafOfComm O')) :=
  unitIsoOf F b (Construction.presheafCoreMonoidal F b)

/-- The forward morphism of the unit comparison. -/
@[stacks 03EL "unit comparison on objects"]
noncomputable abbrev unitComparison :
    (SheafOfModules.pullback.{u} (ringMap F b)).obj
        (𝟙_ (SheafOfModules.{u} (CategoryTheory.Sheaf.ringSheafOfComm O))) ⟶
      𝟙_ (SheafOfModules.{u} (CategoryTheory.Sheaf.ringSheafOfComm O')) :=
  (unitIso F b).hom

/-- The natural tensor comparison for representably flat pullback of module sheaves. -/
@[stacks 03EL "tensor comparison"]
noncomputable abbrev tensorNatIso :
    MonoidalCategory.tensor
        (SheafOfModules.{u} (CategoryTheory.Sheaf.ringSheafOfComm O)) ⋙
      SheafOfModules.pullback.{u} (ringMap F b) ≅
    Functor.prod (SheafOfModules.pullback.{u} (ringMap F b))
        (SheafOfModules.pullback.{u} (ringMap F b)) ⋙
      MonoidalCategory.tensor
        (SheafOfModules.{u} (CategoryTheory.Sheaf.ringSheafOfComm O')) :=
  tensorNatIsoOf F b (Construction.presheafCoreMonoidal F b)

/-- The tensor comparison on two module sheaves under representably flat pullback. -/
@[stacks 03EL "tensor comparison on objects"]
noncomputable abbrev tensorIso
    (M N : SheafOfModules.{u} (CategoryTheory.Sheaf.ringSheafOfComm O)) :
    (SheafOfModules.pullback.{u} (ringMap F b)).obj (M ⊗ N) ≅
      ((SheafOfModules.pullback.{u} (ringMap F b)).obj M ⊗
        (SheafOfModules.pullback.{u} (ringMap F b)).obj N) :=
  tensorIsoOf F b (Construction.presheafCoreMonoidal F b) M N

/-- The forward morphism of the tensor comparison. -/
@[stacks 03EL "tensor comparison on objects"]
noncomputable abbrev tensorComparison
    (M N : SheafOfModules.{u} (CategoryTheory.Sheaf.ringSheafOfComm O)) :
    (SheafOfModules.pullback.{u} (ringMap F b)).obj (M ⊗ N) ⟶
      ((SheafOfModules.pullback.{u} (ringMap F b)).obj M ⊗
        (SheafOfModules.pullback.{u} (ringMap F b)).obj N) :=
  (tensorIso F b M N).hom

end Compatibility

end SheafOfModules.Pullback
