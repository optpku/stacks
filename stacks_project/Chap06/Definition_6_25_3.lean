module

public import Mathlib.Geometry.RingedSpace.Basic
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open Opposite TopologicalSpace

namespace AlgebraicGeometry

variable {X Y Z : RingedSpace.{u, v}} (f : X ⟶ Y) (g : Y ⟶ Z)

/- Domain-style sampling for Definition 6.25.3:
- primary domain: categorical composition of morphisms in `RingedSpace` and the resulting formulas
  on the underlying `SheafedSpace` and topological-space components;
- sampled owner declarations:
  `CategoryStruct.comp`,
  `InducedCategory.comp_hom`,
  `SheafedSpace.comp_hom_base`,
  `SheafedSpace.comp_hom_c_app'`;
- owner abstraction: categorical composition in `RingedSpace`;
- primitive data: composable morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`;
- derived API: the formulas for the underlying `SheafedSpace` morphism, the underlying continuous
  map, and the sectionwise structure-sheaf map of `f ≫ g`.

Source/core/bridge triage:
- `source-facing`: the Stacks formula saying that the base map and structure-sheaf map of
  `f ≫ g` are the corresponding composites;
- `core/canonical`: categorical composition in `RingedSpace`;
- `bridge/view`: the induced component formulas
  `InducedCategory.comp_hom`, `SheafedSpace.comp_hom_base`, and
  `SheafedSpace.comp_hom_c_app'`.

This item only recalls canonical owner data already present upstream, so the refined file should
stay recall-shaped and avoid any parallel local wrapper for composition. -/

/- Definition 6.25.3: the composition of morphisms of ringed spaces is the canonical categorical
composition `f ≫ g : X ⟶ Z`. This matches the source formula whose underlying continuous map is
`f.hom.base ≫ g.hom.base` and whose structure-sheaf map is the composite owned by
`SheafedSpace.comp_hom_c_app' f g`. -/
@[stacks 0093 "composition of morphisms of ringed spaces"]
#check (f ≫ g : X ⟶ Z)

/- On the underlying `SheafedSpace`, composition is the canonical induced-category composition. -/
@[stacks 0093 "underlying sheafed-space morphism of a composite"]
#check (InducedCategory.comp_hom f g : (f ≫ g).hom = f.hom ≫ g.hom)

/- On underlying continuous maps, the composite is first `f.hom.base`, then `g.hom.base`. -/
@[stacks 0093 "underlying continuous map of a composite"]
#check (SheafedSpace.comp_hom_base f g :
  (f ≫ g).hom.base = f.hom.base ≫ g.hom.base)

variable (U : Opens Z)

/- On sections over `U`, the structure-sheaf component is the canonical composite described by
`SheafedSpace.comp_hom_c_app' f g U`. -/
@[stacks 0093 "structure-sheaf component of a composite"]
#check (SheafedSpace.comp_hom_c_app' f g U)

end AlgebraicGeometry
