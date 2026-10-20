/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Henselization.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.InverseImageStalk

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {S' S : Scheme.{u}} (g : S' ⟶ S)
variable [HasWeakSheafify S'.smallEtaleTopology (Type u)]
variable [∀ P : S.Etaleᵒᵖ ⥤ Type u,
  (smallEtalePullback g).op.HasLeftKanExtension P]

/-- Canonical specialization of étale stalks commutes with inverse image under the
canonical stalk identifications at a geometric point and a point of its strict henselization. -/
theorem étaleSpecializationMap_inverseImage (sbar' : GeometricPoint S')
    (tbar' : GeometricPoint (strictHenselizationAt S' sbar'))
    (F : Sheaf S.smallEtaleTopology (Type u)) :
    let tbar := tbar'.map (StrictHenselization.toScheme S' sbar')
    let inverseImage := ((smallEtalePullback g).sheafPullback (Type u)
      S.smallEtaleTopology S'.smallEtaleTopology).obj F
    let sourceSpecialization := (StrictHenselianNeighborhood.canonical sbar').specializationPoint
      (t := tbar) tbar'.hom
      (by exact (GeometricPoint.map_hom tbar' (StrictHenselization.toScheme S' sbar')).symm)
    let targetSpecialization :=
      (StrictHenselianNeighborhood.canonical (sbar'.map g)).specializationPoint
        (t := tbar.map g) (tbar'.hom ≫ StrictHenselization.map g sbar') (by
          change (tbar'.hom ≫ StrictHenselization.map g sbar') ≫
              StrictHenselization.toScheme S (sbar'.map g) =
            (tbar'.hom ≫ StrictHenselization.toScheme S' sbar') ≫ g
          rw [Category.assoc, StrictHenselization.map_toScheme, Category.assoc])
    sourceSpecialization.sheafFiber.app inverseImage ≫
        (smallEtaleInverseImage_stalkIso g tbar F).hom =
      (smallEtaleInverseImage_stalkIso g sbar' F).hom ≫
        targetSpecialization.sheafFiber.app F := sorry

/-- Specializing a germ of an inverse-image étale sheaf and then identifying its stalk
equals identifying the germ first and specializing it along the canonical strict-henselization map. -/
theorem étaleSpecializationMap_inverseImage_apply (sbar' : GeometricPoint S')
    (tbar' : GeometricPoint (strictHenselizationAt S' sbar'))
    (F : Sheaf S.smallEtaleTopology (Type u))
    (element : sbar'.toSmallEtalePoint.sheafFiber.obj
      (((smallEtalePullback g).sheafPullback (Type u)
        S.smallEtaleTopology S'.smallEtaleTopology).obj F)) :
    let tbar := tbar'.map (StrictHenselization.toScheme S' sbar')
    let inverseImage := ((smallEtalePullback g).sheafPullback (Type u)
      S.smallEtaleTopology S'.smallEtaleTopology).obj F
    let sourceSpecialization := (StrictHenselianNeighborhood.canonical sbar').specializationPoint
      (t := tbar) tbar'.hom
      (by exact (GeometricPoint.map_hom tbar' (StrictHenselization.toScheme S' sbar')).symm)
    let targetSpecialization :=
      (StrictHenselianNeighborhood.canonical (sbar'.map g)).specializationPoint
        (t := tbar.map g) (tbar'.hom ≫ StrictHenselization.map g sbar') (by
          change (tbar'.hom ≫ StrictHenselization.map g sbar') ≫
              StrictHenselization.toScheme S (sbar'.map g) =
            (tbar'.hom ≫ StrictHenselization.toScheme S' sbar') ≫ g
          rw [Category.assoc, StrictHenselization.map_toScheme, Category.assoc])
    (smallEtaleInverseImage_stalkIso g tbar F).hom
        (sourceSpecialization.sheafFiber.app inverseImage element) =
      targetSpecialization.sheafFiber.app F
        ((smallEtaleInverseImage_stalkIso g sbar' F).hom element) := sorry

end AlgebraicGeometry.Scheme
