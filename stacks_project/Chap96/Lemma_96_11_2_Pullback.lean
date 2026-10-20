module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Pullback
public import stacks_project.Chap96.Definition_96_6_1_StructureSheaf

/-!
# Pullback of modules on categories fibred in groupoids

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` induces the inverse image
`f⁻¹` of sheaves of modules. Because `f⁻¹ 𝒪_Y ≅ 𝒪_X`, this agrees with `f^*`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}

#check (AlgebraicGeometry.GroupoidsOver.inverseImageStructureSheaf :
  {S : Scheme.{u}} → {X Y : GroupoidsOver S} → (X ⟶ Y) →
    Sheaf (inheritedFppfTopology X) RingCat.{u})

#check (AlgebraicGeometry.GroupoidsOver.structureSheafIso :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y),
    inverseImageStructureSheaf f ≅ structureSheaf X)

#check (AlgebraicGeometry.GroupoidsOver.structureSheafMap :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y),
    structureSheaf X ⟶ inverseImageStructureSheaf f)

#check (AlgebraicGeometry.GroupoidsOver.structureSheafMap_isIso :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y),
    IsIso (structureSheafMap f))

#check (AlgebraicGeometry.GroupoidsOver.modulePullback :
  {S : Scheme.{u}} → {X Y : GroupoidsOver S} → (X ⟶ Y) →
    SheafOfModules.{u} (structureSheaf Y) ⥤ SheafOfModules.{u} (structureSheaf X))

#check (AlgebraicGeometry.GroupoidsOver.modulePullback_eq :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y),
    modulePullback f = SheafOfModules.pushforward (structureSheafMap f))

end AlgebraicGeometry.GroupoidsOver
