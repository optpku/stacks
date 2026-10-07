module

public import stacks_project.Chap59.Definition_59_71_1
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u w

namespace CategoryTheory.Sheaf

/-- Lemma 59.73.4 (1): if `f : X ⟶ Y` is a finite étale morphism of schemes and `F` is a
constructible sheaf of sets on `Xₑₜ`, then `f_* F` is constructible on `Yₑₜ`, where `f_*` is
`(Scheme.smallEtalePullback f).sheafPushforwardContinuous`. -/
@[stacks 095H]
theorem isConstructibleEtaleSet_smallEtalePushforward
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]
    [HasWeakSheafify Y.smallEtaleTopology (Type (u + 1))]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (Type (u + 1))]
    (restrict : ∀ {Z W : Scheme.{u}} (_ : Z ⟶ W),
      Sheaf W.smallEtaleTopology (Type (u + 1)) →
        Sheaf Z.smallEtaleTopology (Type (u + 1)))
    (finiteLocallyConstant : ∀ {Z : Scheme.{u}},
      Sheaf Z.smallEtaleTopology (Type (u + 1)) → Prop)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (hF : IsConstructibleEtaleSet (fun {Z} g ↦ restrict g) finiteLocallyConstant F) :
    IsConstructibleEtaleSet (fun {Z} g ↦ restrict g) finiteLocallyConstant
      (((Scheme.smallEtalePullback f).sheafPushforwardContinuous
        (Type (u + 1)) Y.smallEtaleTopology X.smallEtaleTopology).obj F) :=
  sorry

/-- Lemma 59.73.4 (2): if `f : X ⟶ Y` is a finite étale morphism of schemes and `F` is a
constructible sheaf of abelian groups on `Xₑₜ`, then `f_* F` is constructible on `Yₑₜ`, where
`f_*` is `(Scheme.smallEtalePullback f).sheafPushforwardContinuous`. -/
@[stacks 095H]
theorem isConstructibleEtaleAddCommGrp_smallEtalePushforward
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ U : X.Etale,
      HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ U : Y.Etale,
      HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
    (restrict : ∀ {Z W : Scheme.{u}} (_ : Z ⟶ W),
      Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1} →
        Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (finiteLocallyConstant : ∀ {Z : Scheme.{u}},
      Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1} → Prop)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleEtaleAddCommGrp (fun {Z} g ↦ restrict g) finiteLocallyConstant F) :
    IsConstructibleEtaleAddCommGrp (fun {Z} g ↦ restrict g) finiteLocallyConstant
      (((Scheme.smallEtalePullback f).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} Y.smallEtaleTopology X.smallEtaleTopology).obj F) :=
  sorry

/-- Lemma 59.73.4 (3): if `f : X ⟶ Y` is a finite étale morphism of schemes, `Λ` is Noetherian,
and `F` is a constructible sheaf of `Λ`-modules on `Xₑₜ`, then `f_* F` is constructible on
`Yₑₜ`, where `f_*` is `(Scheme.smallEtalePullback f).sheafPushforwardContinuous`. -/
@[stacks 095H]
theorem isConstructibleEtaleModule_smallEtalePushforward
    {X Y : Scheme.{u}} {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
    (f : X ⟶ Y) [IsFinite f] [Etale f]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
    [∀ U : X.Etale,
      HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
    [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
    [∀ U : Y.Etale,
      HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
    (restrict : ∀ {Z W : Scheme.{u}} (_ : Z ⟶ W),
      Sheaf W.smallEtaleTopology (ModuleCat.{w} Λ) →
        Sheaf Z.smallEtaleTopology (ModuleCat.{w} Λ))
    (finiteTypeLocallyConstant : ∀ {Z : Scheme.{u}},
      Sheaf Z.smallEtaleTopology (ModuleCat.{w} Λ) → Prop)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))
    (hF : IsConstructibleEtaleModule (fun {Z} g ↦ restrict g) finiteTypeLocallyConstant F) :
    IsConstructibleEtaleModule (fun {Z} g ↦ restrict g) finiteTypeLocallyConstant
      (((Scheme.smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{w} Λ) Y.smallEtaleTopology X.smallEtaleTopology).obj F) :=
  sorry

end CategoryTheory.Sheaf
