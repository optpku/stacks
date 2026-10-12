/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplexCategory.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Biproducts indexed by epic and monic simplex morphisms

The indexing types belong to the simplex category, while the construction only asks the
coefficient category for the corresponding finite coproducts or products.  Keeping these
instances in a separate leaf avoids coupling the coefficient-free `EpiMono` API to preadditivity.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace SimplexCategory

variable {C : Type u} [Category.{v} C]

namespace EpiHom

/-- A finite coproduct indexed by epic simplex morphisms canonically determines a biproduct. -/
@[stacks 0190 "biproducts indexed by epic simplex morphisms"]
instance hasBiproduct [Preadditive C] [HasFiniteCoproducts C]
    {X Y : SimplexCategory} (F : EpiHom X Y → C) : HasBiproduct F :=
  HasBiproduct.of_hasCoproduct F

end EpiHom

namespace MonoHom

/-- A finite product indexed by monic simplex morphisms canonically determines a biproduct. -/
@[stacks 0190 "biproducts indexed by monic simplex morphisms"]
instance hasBiproduct [Preadditive C] [HasFiniteProducts C]
    {X Y : SimplexCategory} (F : MonoHom X Y → C) : HasBiproduct F :=
  HasBiproduct.of_hasProduct F

end MonoHom

end SimplexCategory
