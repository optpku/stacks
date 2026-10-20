module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Support.Ind
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u

namespace CategoryTheory.Sheaf

/- Lemma 59.73.14 (1): on a quasi-compact quasi-separated scheme `X`, a torsion abelian
sheaf with zero geometric stalk at a generic point of an irreducible component is a filtered
colimit of constructible abelian sheaves supported in closed subsets avoiding that point. -/
@[stacks 0F0M] #check
  (CategoryTheory.Sheaf.isConstructibleEtaleAddCommGrp_ind_supportAway :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
      (ηbar : Scheme.GeometricPoint X)
      (hη : IsGenericPoint ηbar.image (irreducibleComponent ηbar.image))
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (hF : IsLocallyTorsion F)
      (h0 : IsZero (geometricStalkAddCommGrp F ηbar)),
      ObjectProperty.ind.{u + 1}
        (IsConstructibleEtaleAddCommGrp.SupportAway ηbar.image) F)

/- Lemma 59.73.14 (2): on a quasi-compact quasi-separated scheme `X` and a Noetherian ring
`Λ`, a module sheaf with zero geometric stalk at a generic point of an irreducible component is a
filtered colimit of constructible module sheaves supported in closed subsets avoiding that point. -/
@[stacks 0F0M] #check
  (CategoryTheory.Sheaf.isConstructibleEtaleModule_ind_supportAway :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      {Λ : Type (u + 1)} [Ring Λ] [IsNoetherianRing Λ]
      [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
      [∀ (Y : Scheme.{u}) (U : Y.Etale),
        HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
      [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z)
        (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ),
        (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
      (ηbar : Scheme.GeometricPoint X)
      (hη : IsGenericPoint ηbar.image (irreducibleComponent ηbar.image))
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (h0 : IsZero (geometricStalkModule F ηbar)),
      ObjectProperty.ind.{u + 1}
        (IsConstructibleEtaleModule.SupportAway ηbar.image) F)

end CategoryTheory.Sheaf
