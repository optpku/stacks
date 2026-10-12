/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v w

namespace CategoryTheory.Sheaf

variable {X Y : Scheme.{u}}

/-- The inverse-image functor on sheaves over the small étale sites induced by a scheme morphism. -/
noncomputable abbrev smallEtaleInverseImage
    (f : X ⟶ Y) (D : Type w) [Category.{v} D]
    [HasWeakSheafify X.smallEtaleTopology D]
    [∀ (P : Y.Etaleᵒᵖ ⥤ D), (Scheme.smallEtalePullback f).op.HasLeftKanExtension P] :
    Sheaf Y.smallEtaleTopology D ⥤ Sheaf X.smallEtaleTopology D :=
  (Scheme.smallEtalePullback f).sheafPullback D Y.smallEtaleTopology X.smallEtaleTopology

/-- Pullback preserves constructibility of finite locally constant set-valued étale sheaves. -/
theorem isConstructibleEtaleSet_sheafPullback
    (f : X ⟶ Y)
    [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (Type (u + 1))]
    [∀ (Z W : Scheme.{u}) (g : Z ⟶ W) (P : W.Etaleᵒᵖ ⥤ Type (u + 1)),
      (Scheme.smallEtalePullback g).op.HasLeftKanExtension P]
    (F : Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (hF : IsConstructibleEtaleSet (X := Y)
      (fun {Z} g ↦ (smallEtaleInverseImage g (Type (u + 1))).obj)
      (fun {Z} G ↦ IsFiniteLocallyConstant G) F) :
    IsConstructibleEtaleSet (X := X)
      (fun {Z} g ↦ (smallEtaleInverseImage g (Type (u + 1))).obj)
      (fun {Z} G ↦ IsFiniteLocallyConstant G)
      ((smallEtaleInverseImage f (Type (u + 1))).obj F) := sorry

/-- Pullback preserves constructibility of finite locally constant abelian-group-valued étale
sheaves. -/
theorem isConstructibleEtaleAddCommGrp_sheafPullback
    (f : X ⟶ Y)
    [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ (Z W : Scheme.{u}) (g : Z ⟶ W) (P : W.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      (Scheme.smallEtalePullback g).op.HasLeftKanExtension P]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleEtaleAddCommGrp (X := Y)
      (fun {Z} g ↦ (smallEtaleInverseImage g AddCommGrpCat.{u + 1}).obj)
      (fun {Z} G ↦ IsFiniteLocallyConstantAddCommGrp G) F) :
    IsConstructibleEtaleAddCommGrp (X := X)
      (fun {Z} g ↦ (smallEtaleInverseImage g AddCommGrpCat.{u + 1}).obj)
      (fun {Z} G ↦ IsFiniteLocallyConstantAddCommGrp G)
      ((smallEtaleInverseImage f AddCommGrpCat.{u + 1}).obj F) := sorry

/-- Pullback preserves constructibility of finite-type locally constant étale sheaves of modules
over a Noetherian ring. -/
theorem isConstructibleEtaleModule_sheafPullback
    (f : X ⟶ Y) {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
    [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{w} Λ)]
    [∀ (Z : Scheme.{u}) (U : Z.Etale),
      HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
    [∀ (Z W : Scheme.{u}) (g : Z ⟶ W) (P : W.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
      (Scheme.smallEtalePullback g).op.HasLeftKanExtension P]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ))
    (hF : IsConstructibleEtaleModule (X := Y)
      (fun {Z} g ↦ (smallEtaleInverseImage g (ModuleCat.{w} Λ)).obj)
      (fun {Z} G ↦ IsFiniteTypeLocallyConstantModule G) F) :
    IsConstructibleEtaleModule (X := X)
      (fun {Z} g ↦ (smallEtaleInverseImage g (ModuleCat.{w} Λ)).obj)
      (fun {Z} G ↦ IsFiniteTypeLocallyConstantModule G)
      ((smallEtaleInverseImage f (ModuleCat.{w} Λ)).obj F) := sorry

end CategoryTheory.Sheaf
