module

public import ReasLib.Topology.Category.TopCat.DiagramOpens

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v w

namespace TopCat.DiagramOpens

variable {C : Type u} [Category.{v} C] (F : C ⥤ TopCat.{w})

#check (DiagramOpens : (C ⥤ TopCat.{w}) → Type _)
#check (base F : DiagramOpens F → C)
#check (opens F : (U : DiagramOpens F) → Opens (F.obj U.base))
#check (ofOpens F : ∀ c, Opens (F.obj c) → DiagramOpens F)
#check (@Hom C _ F)
#check Hom.base
#check Hom.mapsTo
#check homMk
#check Hom.preimage
#check (fiber F : ∀ c, Opens (F.obj c) ⥤ DiagramOpens F)
#check Hom.toContinuousMap
#check (toTopCat F : DiagramOpens F ⥤ TopCat.{w})

end TopCat.DiagramOpens
