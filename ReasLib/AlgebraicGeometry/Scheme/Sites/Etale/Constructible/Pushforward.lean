module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocallyConstantPushforward
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u w

namespace CategoryTheory.Sheaf

/-- A finite étale morphism preserves constructibility of finite locally constant sheaves of sets
on the small étale site under continuous direct image. -/
theorem isConstructibleEtaleSet_smallEtalePushforward
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
    [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (Type (u + 1))]
    [∀ (Z W : Scheme.{u}) (g : Z ⟶ W) (P : W.Etaleᵒᵖ ⥤ Type (u + 1)),
      (Scheme.smallEtalePullback g).op.HasLeftKanExtension P]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (hF : IsConstructibleEtaleSet (X := X)
      (fun {Z} g ↦ (smallEtaleInverseImage g (Type (u + 1))).obj)
      (fun {Z} G ↦ IsFiniteLocallyConstant G) F) :
    IsConstructibleEtaleSet (X := Y)
      (fun {Z} g ↦ (smallEtaleInverseImage g (Type (u + 1))).obj)
      (fun {Z} G ↦ IsFiniteLocallyConstant G)
      (((Scheme.smallEtalePullback f).sheafPushforwardContinuous
        (Type (u + 1)) Y.smallEtaleTopology X.smallEtaleTopology).obj F) := sorry

/-- A finite étale morphism preserves constructibility of finite locally constant abelian-group
sheaves on the small étale site under continuous direct image. -/
theorem isConstructibleEtaleAddCommGrp_smallEtalePushforward
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
    [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ (Z W : Scheme.{u}) (g : Z ⟶ W) (P : W.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      (Scheme.smallEtalePullback g).op.HasLeftKanExtension P]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleEtaleAddCommGrp (X := X)
      (fun {Z} g ↦ (smallEtaleInverseImage g AddCommGrpCat.{u + 1}).obj)
      (fun {Z} G ↦ IsFiniteLocallyConstantAddCommGrp G) F) :
    IsConstructibleEtaleAddCommGrp (X := Y)
      (fun {Z} g ↦ (smallEtaleInverseImage g AddCommGrpCat.{u + 1}).obj)
      (fun {Z} G ↦ IsFiniteLocallyConstantAddCommGrp G)
      (((Scheme.smallEtalePullback f).sheafPushforwardContinuous
        (AddCommGrpCat.{u + 1}) Y.smallEtaleTopology X.smallEtaleTopology).obj F) := sorry

/-- A finite étale morphism preserves constructibility of finite-type locally constant sheaves of
modules over a Noetherian ring on the small étale site under continuous direct image. -/
theorem isConstructibleEtaleModule_smallEtalePushforward
    {X Y : Scheme.{u}} {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
    (f : X ⟶ Y) [IsFinite f] [Etale f]
    [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{w} Λ)]
    [∀ (Z : Scheme.{u}) (U : Z.Etale),
      HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
    [∀ (Z W : Scheme.{u}) (g : Z ⟶ W) (P : W.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
      (Scheme.smallEtalePullback g).op.HasLeftKanExtension P]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))
    (hF : IsConstructibleEtaleModule (X := X)
      (fun {Z} g ↦ (smallEtaleInverseImage g (ModuleCat.{w} Λ)).obj)
      (fun {Z} G ↦ IsFiniteTypeLocallyConstantModule G) F) :
    IsConstructibleEtaleModule (X := Y)
      (fun {Z} g ↦ (smallEtaleInverseImage g (ModuleCat.{w} Λ)).obj)
      (fun {Z} G ↦ IsFiniteTypeLocallyConstantModule G)
      (((Scheme.smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{w} Λ) Y.smallEtaleTopology X.smallEtaleTopology).obj F) := sorry

/-- A finite finitely presented morphism preserves constructibility of sheaves of sets on the
small étale site under continuous direct image. -/
theorem isConstructibleEtaleSet_smallEtalePushforward_of_finite_fp
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [LocallyOfFinitePresentation f]
    [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (Type (u + 1))]
    [∀ (Z : Scheme.{u}) (U : Z.Etale),
      HasWeakSheafify (Z.smallEtaleTopology.over U) (Type (u + 1))]
    [∀ (Z W : Scheme.{u}) (g : Z ⟶ W) (P : W.Etaleᵒᵖ ⥤ Type (u + 1)),
      (Scheme.smallEtalePullback g).op.HasLeftKanExtension P]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (hF : IsConstructibleEtaleSet (X := X)
      (fun {Z} g ↦ (smallEtaleInverseImage g (Type (u + 1))).obj)
      (fun {Z} G ↦ IsFiniteLocallyConstant G) F) :
    IsConstructibleEtaleSet (X := Y)
      (fun {Z} g ↦ (smallEtaleInverseImage g (Type (u + 1))).obj)
      (fun {Z} G ↦ IsFiniteLocallyConstant G)
      (((Scheme.smallEtalePullback f).sheafPushforwardContinuous
        (Type (u + 1)) Y.smallEtaleTopology X.smallEtaleTopology).obj F) := sorry

/-- A finite finitely presented morphism preserves constructibility of sheaves of abelian groups
on the small étale site under continuous direct image. -/
theorem isConstructibleEtaleAddCommGrp_smallEtalePushforward_of_finite_fp
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [LocallyOfFinitePresentation f]
    [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ (Z : Scheme.{u}) (U : Z.Etale),
      HasWeakSheafify (Z.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
    [∀ (Z W : Scheme.{u}) (g : Z ⟶ W) (P : W.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      (Scheme.smallEtalePullback g).op.HasLeftKanExtension P]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleEtaleAddCommGrp (X := X)
      (fun {Z} g ↦ (smallEtaleInverseImage g AddCommGrpCat.{u + 1}).obj)
      (fun {Z} G ↦ IsFiniteLocallyConstantAddCommGrp G) F) :
    IsConstructibleEtaleAddCommGrp (X := Y)
      (fun {Z} g ↦ (smallEtaleInverseImage g AddCommGrpCat.{u + 1}).obj)
      (fun {Z} G ↦ IsFiniteLocallyConstantAddCommGrp G)
      (((Scheme.smallEtalePullback f).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} Y.smallEtaleTopology X.smallEtaleTopology).obj F) := sorry

/-- A finite finitely presented morphism preserves constructibility of sheaves of modules over
a Noetherian ring on the small étale site under continuous direct image. -/
theorem isConstructibleEtaleModule_smallEtalePushforward_of_finite_fp
    {X Y : Scheme.{u}} {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
    (f : X ⟶ Y) [IsFinite f] [LocallyOfFinitePresentation f]
    [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{w} Λ)]
    [∀ (Z : Scheme.{u}) (U : Z.Etale),
      HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
    [∀ (Z W : Scheme.{u}) (g : Z ⟶ W) (P : W.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
      (Scheme.smallEtalePullback g).op.HasLeftKanExtension P]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))
    (hF : IsConstructibleEtaleModule (X := X)
      (fun {Z} g ↦ (smallEtaleInverseImage g (ModuleCat.{w} Λ)).obj)
      (fun {Z} G ↦ IsFiniteTypeLocallyConstantModule G) F) :
    IsConstructibleEtaleModule (X := Y)
      (fun {Z} g ↦ (smallEtaleInverseImage g (ModuleCat.{w} Λ)).obj)
      (fun {Z} G ↦ IsFiniteTypeLocallyConstantModule G)
      (((Scheme.smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{w} Λ) Y.smallEtaleTopology X.smallEtaleTopology).obj F) := sorry

end CategoryTheory.Sheaf
