module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Ind
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u w

namespace CategoryTheory.Sheaf

/- Lemma 59.73.2 (1): on a quasi-compact quasi-separated scheme `X`, every sheaf of sets on
`Xₑₜ` is a filtered colimit of constructible sheaves of sets. -/
@[stacks 03SA] #check
  (CategoryTheory.Sheaf.isConstructibleEtaleSet_ind :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
      (F : Sheaf X.smallEtaleTopology (Type (u + 1))),
      ObjectProperty.ind.{u + 1}
        (fun G ↦ IsConstructibleEtaleSet
          (fun {Y} f ↦
            ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} G ↦ IsFiniteLocallyConstant G) G) F)

/- Lemma 59.73.2 (2): on a quasi-compact quasi-separated scheme `X`, every torsion abelian
sheaf on `Xₑₜ` is a filtered colimit of constructible abelian sheaves. -/
@[stacks 03SA] #check
  (CategoryTheory.Sheaf.isConstructibleEtaleAddCommGrp_ind :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      IsLocallyTorsion F →
        ObjectProperty.ind.{u + 1}
          (fun G ↦ IsConstructibleEtaleAddCommGrp
            (fun {Y} f ↦
              ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
                X.smallEtaleTopology Y.smallEtaleTopology).obj)
            (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) G) F)

/- Lemma 59.73.2 (3): on a quasi-compact quasi-separated scheme `X` and a Noetherian ring `Λ`,
every sheaf of `Λ`-modules on `Xₑₜ` is a filtered colimit of constructible sheaves of `Λ`-modules. -/
@[stacks 03SA] #check
  (CategoryTheory.Sheaf.isConstructibleEtaleModule_ind :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
      [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
      [∀ (Y : Scheme.{u}) (U : Y.Etale),
        HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
      [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z)
        (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
        (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)),
      ObjectProperty.ind.{max (u + 1) w}
        (fun G ↦ IsConstructibleEtaleModule
          (fun {Y} f ↦
            ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} G ↦ IsFiniteTypeLocallyConstantModule G) G) F)

end CategoryTheory.Sheaf
