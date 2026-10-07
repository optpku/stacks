module

public import stacks_project.Chap59.Lemma_59_71_5
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u w

namespace CategoryTheory.Sheaf

variable {X Y : Scheme.{u}}
variable [CompactSpace X] [QuasiSeparatedSpace X]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- Lemma 59.73.3 (1): if `f : X ⟶ Y` is a surjective morphism of quasi-compact quasi-separated
schemes and `F` is a sheaf of sets on `Yₑₜ`, then `F` is constructible if and only if the inverse
image `(smallEtaleInverseImage f _).obj F` is constructible. -/
@[stacks 095Q]
theorem isConstructibleEtaleSet_iff_smallEtaleInverseImage
    (f : X ⟶ Y) [Surjective f]
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    [∀ (P : Y.Etaleᵒᵖ ⥤ Type (u + 1)),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    (restrict : ∀ {Z W : Scheme.{u}} (_ : Z ⟶ W),
      Sheaf W.smallEtaleTopology (Type (u + 1)) →
        Sheaf Z.smallEtaleTopology (Type (u + 1)))
    (finiteLocallyConstant : ∀ {Z : Scheme.{u}},
      Sheaf Z.smallEtaleTopology (Type (u + 1)) → Prop)
    (F : Sheaf Y.smallEtaleTopology (Type (u + 1))) :
    IsConstructibleEtaleSet (fun {Z} g ↦ restrict g) finiteLocallyConstant F ↔
      IsConstructibleEtaleSet (fun {Z} g ↦ restrict g) finiteLocallyConstant
        ((smallEtaleInverseImage f (Type (u + 1))).obj F) :=
  sorry

/-- Lemma 59.73.3 (2): if `f : X ⟶ Y` is a surjective morphism of quasi-compact quasi-separated
schemes and `F` is an abelian sheaf on `Yₑₜ`, then `F` is constructible if and only if the inverse
image `(smallEtaleInverseImage f _).obj F` is constructible. -/
@[stacks 095Q]
theorem isConstructibleEtaleAddCommGrp_iff_smallEtaleInverseImage
    (f : X ⟶ Y) [Surjective f]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ (P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    (restrict : ∀ {Z W : Scheme.{u}} (_ : Z ⟶ W),
      Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1} →
        Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (finiteLocallyConstant : ∀ {Z : Scheme.{u}},
      Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1} → Prop)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsConstructibleEtaleAddCommGrp (fun {Z} g ↦ restrict g) finiteLocallyConstant F ↔
      IsConstructibleEtaleAddCommGrp (fun {Z} g ↦ restrict g) finiteLocallyConstant
        ((smallEtaleInverseImage f AddCommGrpCat.{u + 1}).obj F) :=
  sorry

/-- Lemma 59.73.3 (3): if `f : X ⟶ Y` is a surjective morphism of quasi-compact quasi-separated
schemes, `Λ` is Noetherian, and `F` is a sheaf of `Λ`-modules on `Yₑₜ`, then `F` is constructible
if and only if the inverse image `(smallEtaleInverseImage f _).obj F` is constructible. -/
@[stacks 095Q]
theorem isConstructibleEtaleModule_iff_smallEtaleInverseImage
    (f : X ⟶ Y) [Surjective f] {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
    [∀ (P : Y.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    (restrict : ∀ {Z W : Scheme.{u}} (_ : Z ⟶ W),
      Sheaf W.smallEtaleTopology (ModuleCat.{w} Λ) →
        Sheaf Z.smallEtaleTopology (ModuleCat.{w} Λ))
    (finiteTypeLocallyConstant : ∀ {Z : Scheme.{u}},
      Sheaf Z.smallEtaleTopology (ModuleCat.{w} Λ) → Prop)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)) :
    IsConstructibleEtaleModule (fun {Z} g ↦ restrict g) finiteTypeLocallyConstant F ↔
      IsConstructibleEtaleModule (fun {Z} g ↦ restrict g) finiteTypeLocallyConstant
        ((smallEtaleInverseImage f (ModuleCat.{w} Λ)).obj F) :=
  sorry

end CategoryTheory.Sheaf
