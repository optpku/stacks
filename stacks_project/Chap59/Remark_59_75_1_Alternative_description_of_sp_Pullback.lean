module

public import stacks_project.Chap59.Definition_59_29_6
public import stacks_project.Chap59.Remark_59_75_2_Yet_another_description_of_sp_Map
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SectionsPullback

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- Inverse image of an étale sheaf of sets along a scheme morphism. -/
abbrev smallEtaleSheafPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasWeakSheafify Y.smallEtaleTopology (Type u)]
    [∀ P : Y.Etaleᵒᵖ ⥤ Type u, (smallEtalePullback f).op.HasLeftKanExtension P]
    (G : Sheaf Y.smallEtaleTopology (Type u)) :
    Sheaf X.smallEtaleTopology (Type u) :=
  (Sheaf.smallEtaleInverseImage f (Type u)).obj G

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [HasWeakSheafify X.smallEtaleTopology (Type u)]
variable [HasWeakSheafify Y.smallEtaleTopology (Type u)]
variable [∀ P : Y.Etaleᵒᵖ ⥤ Type u, (smallEtalePullback f).op.HasLeftKanExtension P]
variable (G : Sheaf Y.smallEtaleTopology (Type u))

/- Sections pullback is owned by the shared étale sections API. -/
#check (AlgebraicGeometry.Scheme.etaleSectionsPullback f G :
  etaleGlobalSections G → etalePullbackIdentitySections f G)

end AlgebraicGeometry.Scheme

end
