/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Specialization.InverseImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 59.75.4: canonical specialization commutes with inverse image under the
canonical identifications of geometric stalks. -/
@[stacks 0GJ6] #check
  (AlgebraicGeometry.Scheme.étaleSpecializationMap_inverseImage :
    ∀ {S' S : Scheme.{u}} (g : S' ⟶ S)
      [HasWeakSheafify S'.smallEtaleTopology (Type u)]
      [∀ P : S.Etaleᵒᵖ ⥤ Type u,
        (Scheme.smallEtalePullback g).op.HasLeftKanExtension P]
      (sbar' : Scheme.GeometricPoint S')
      (tbar' : Scheme.GeometricPoint (Scheme.strictHenselizationAt S' sbar'))
      (F : Sheaf S.smallEtaleTopology (Type u)),
      let tbar := tbar'.map (Scheme.StrictHenselization.toScheme S' sbar')
      let inverseImage := ((Scheme.smallEtalePullback g).sheafPullback (Type u)
        S.smallEtaleTopology S'.smallEtaleTopology).obj F
      let sourceSpecialization :=
        (Scheme.StrictHenselianNeighborhood.canonical sbar').specializationPoint
          (t := tbar) tbar'.hom (by
            exact (Scheme.GeometricPoint.map_hom tbar'
              (Scheme.StrictHenselization.toScheme S' sbar')).symm)
      let targetSpecialization :=
        (Scheme.StrictHenselianNeighborhood.canonical (sbar'.map g)).specializationPoint
          (t := tbar.map g) (tbar'.hom ≫ Scheme.StrictHenselization.map g sbar') (by
            change (tbar'.hom ≫ Scheme.StrictHenselization.map g sbar') ≫
                Scheme.StrictHenselization.toScheme S (sbar'.map g) =
              (tbar'.hom ≫ Scheme.StrictHenselization.toScheme S' sbar') ≫ g
            rw [Category.assoc, Scheme.StrictHenselization.map_toScheme, Category.assoc])
      sourceSpecialization.sheafFiber.app inverseImage ≫
          (Scheme.smallEtaleInverseImage_stalkIso g tbar F).hom =
        (Scheme.smallEtaleInverseImage_stalkIso g sbar' F).hom ≫
          targetSpecialization.sheafFiber.app F)
