/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite.Closure
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u v w

namespace CategoryTheory.Sheaf

variable (X : Scheme.{u})

section SetValued

/-- Constructible sheaves of sets on the small étale site of a scheme are closed under limits
indexed by a finite category. -/
instance constructibleEtaleSet_isClosedUnderLimits
    (K : Type v) [SmallCategory K] [FinCategory K] :
    IsClosedUnderLimitsOfShape
      (fun F : Sheaf X.smallEtaleTopology (Type (u + 1)) ↦
        IsConstructibleEtaleSet
          (fun {Y} f ↦
            ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} G ↦ IsFiniteLocallyConstant G) F) K := sorry

/-- Constructible sheaves of sets on the small étale site of a scheme are closed under colimits
indexed by a finite category. -/
instance constructibleEtaleSet_isClosedUnderColimits
    (K : Type v) [SmallCategory K] [FinCategory K] :
    IsClosedUnderColimitsOfShape
      (fun F : Sheaf X.smallEtaleTopology (Type (u + 1)) ↦
        IsConstructibleEtaleSet
          (fun {Y} f ↦
            ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} G ↦ IsFiniteLocallyConstant G) F) K := sorry

end SetValued

section SetValuedNoetherian

/-- On a Noetherian scheme, constructible étale sheaves of sets are closed under subobjects. -/
instance constructibleEtaleSet_isClosedUnderSubobjects [IsNoetherian X] :
    IsClosedUnderSubobjects
      (fun F : Sheaf X.smallEtaleTopology (Type (u + 1)) ↦
        IsConstructibleEtaleSet
          (fun {Y} f ↦
            ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} G ↦ IsFiniteLocallyConstant G) F) := sorry

/-- On a Noetherian scheme, constructible étale sheaves of sets are closed under quotients. -/
instance constructibleEtaleSet_isClosedUnderQuotients [IsNoetherian X] :
    IsClosedUnderQuotients
      (fun F : Sheaf X.smallEtaleTopology (Type (u + 1)) ↦
        IsConstructibleEtaleSet
          (fun {Y} f ↦
            ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} G ↦ IsFiniteLocallyConstant G) F) := by
  let P : ObjectProperty (Sheaf X.smallEtaleTopology (Type (u + 1))) :=
    fun F ↦ IsConstructibleEtaleSet
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {_Y} G ↦ IsFiniteLocallyConstant G) F
  change P.IsClosedUnderQuotients
  refine ⟨fun {F G} f _ hF ↦ ?_⟩
  have hprod : P (F ⨯ F) :=
    P.prop_limit (pair F F) (by rintro ⟨_ | _⟩ <;> exact hF)
  have hrel : P (pullback f f) :=
    P.prop_of_mono (prod.lift (pullback.fst f f) (pullback.snd f f)) hprod
  exact P.prop_of_isColimit
    ((IsKernelPair.of_hasPullback f).toCoequalizer (regularEpiOfEpi f))
    (by
      rintro (_ | _)
      · exact hrel
      · exact hF)

end SetValuedNoetherian

section AbelianGroups

variable [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- Constructible abelian sheaves on the small étale site of a scheme form a weak Serre class. -/
instance constructibleEtaleAddCommGrp_isWeakSerreClass :
    IsWeakSerreClass
      (fun F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ↦
        IsConstructibleEtaleAddCommGrp
          (fun {Y} f ↦
            ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) F) := sorry

/-- On a Noetherian scheme, constructible étale abelian sheaves form a Serre class. -/
instance constructibleEtaleAddCommGrp_isSerreClass [IsNoetherian X] :
    IsSerreClass
      (fun F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ↦
        IsConstructibleEtaleAddCommGrp
          (fun {Y} f ↦
            ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) F) := sorry

end AbelianGroups

section Modules

variable {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))]
variable [∀ (Y : Scheme.{u}) (f : Y ⟶ X) (P : X.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]

/-- Constructible sheaves of modules over a Noetherian ring on the small étale site of a scheme
form a weak Serre class. -/
instance constructibleEtaleModule_isWeakSerreClass :
    IsWeakSerreClass
      (fun F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ) ↦
        IsConstructibleEtaleModule
          (fun {Y} f ↦
            ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)) ↦
            IsFiniteTypeLocallyConstantModule G) F) := sorry

/-- On a Noetherian scheme and over a Noetherian ring, constructible étale module sheaves form a
Serre class. -/
instance constructibleEtaleModule_isSerreClass [IsNoetherian X] :
    IsSerreClass
      (fun F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ) ↦
        IsConstructibleEtaleModule
          (fun {Y} f ↦
            ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)) ↦
            IsFiniteTypeLocallyConstantModule G) F) := sorry

end Modules

end CategoryTheory.Sheaf
