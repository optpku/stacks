/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v w

namespace CategoryTheory.Sheaf

variable {X Y : Scheme.{u}}

/- Lemma 59.71.5 (1): if `F` is a constructible sheaf of sets on `Yₑₜ`, then the inverse image
along `f : X ⟶ Y` is a constructible sheaf of sets on `Xₑₜ`. -/
@[stacks 095G] #check (CategoryTheory.Sheaf.isConstructibleEtaleSet_sheafPullback :
    ∀ (f : X ⟶ Y)
    [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (Type (u + 1))]
    [∀ (Z W : Scheme.{u}) (g : Z ⟶ W) (P : W.Etaleᵒᵖ ⥤ Type (u + 1)),
      (Scheme.smallEtalePullback g).op.HasLeftKanExtension P]
    (F : Sheaf Y.smallEtaleTopology (Type (u + 1))),
    IsConstructibleEtaleSet (X := Y)
      (fun {Z} g ↦ (smallEtaleInverseImage g (Type (u + 1))).obj)
      (fun {Z} G ↦ IsFiniteLocallyConstant G) F →
    IsConstructibleEtaleSet (X := X)
      (fun {Z} g ↦ (smallEtaleInverseImage g (Type (u + 1))).obj)
      (fun {Z} G ↦ IsFiniteLocallyConstant G)
      ((smallEtaleInverseImage f (Type (u + 1))).obj F))

/- Lemma 59.71.5 (2): if `F` is a constructible sheaf of abelian groups on `Yₑₜ`, then the
inverse image along `f : X ⟶ Y` is a constructible sheaf of abelian groups on `Xₑₜ`. -/
@[stacks 095G] #check (CategoryTheory.Sheaf.isConstructibleEtaleAddCommGrp_sheafPullback :
    ∀ (f : X ⟶ Y)
    [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ (Z W : Scheme.{u}) (g : Z ⟶ W) (P : W.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      (Scheme.smallEtalePullback g).op.HasLeftKanExtension P]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}),
    IsConstructibleEtaleAddCommGrp (X := Y)
      (fun {Z} g ↦ (smallEtaleInverseImage g AddCommGrpCat.{u + 1}).obj)
      (fun {Z} G ↦ IsFiniteLocallyConstantAddCommGrp G) F →
    IsConstructibleEtaleAddCommGrp (X := X)
      (fun {Z} g ↦ (smallEtaleInverseImage g AddCommGrpCat.{u + 1}).obj)
      (fun {Z} G ↦ IsFiniteLocallyConstantAddCommGrp G)
      ((smallEtaleInverseImage f AddCommGrpCat.{u + 1}).obj F))

/- Lemma 59.71.5 (3): if `Λ` is Noetherian and `F` is a constructible sheaf of `Λ`-modules on
`Yₑₜ`, then the inverse image is a constructible sheaf of `Λ`-modules on `Xₑₜ`. -/
@[stacks 095G] #check (CategoryTheory.Sheaf.isConstructibleEtaleModule_sheafPullback :
    ∀ (f : X ⟶ Y) {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
    [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{w} Λ)]
    [∀ (Z : Scheme.{u}) (U : Z.Etale),
      HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
    [∀ (Z W : Scheme.{u}) (g : Z ⟶ W) (P : W.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
      (Scheme.smallEtalePullback g).op.HasLeftKanExtension P]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)),
    IsConstructibleEtaleModule (X := Y)
      (fun {Z} g ↦ (smallEtaleInverseImage g (ModuleCat.{w} Λ)).obj)
      (fun {Z} G ↦ IsFiniteTypeLocallyConstantModule G) F →
    IsConstructibleEtaleModule (X := X)
      (fun {Z} g ↦ (smallEtaleInverseImage g (ModuleCat.{w} Λ)).obj)
      (fun {Z} G ↦ IsFiniteTypeLocallyConstantModule G)
      ((smallEtaleInverseImage f (ModuleCat.{w} Λ)).obj F))

end CategoryTheory.Sheaf
