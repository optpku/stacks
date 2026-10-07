module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.Legs

/-!
# Structural computations for leg transport

Comparison-map formulas for transporting a categorical pullback along isomorphic cospan legs.
-/

@[expose] public section

namespace CategoryTheory
open CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback
namespace Limits.CategoricalPullback
section EquivalenceTransportComputations
variable {A₀ B₀ D₀ : Type*} [Category A₀] [Category B₀] [Category D₀]
/-- The structural forward map after transport along isomorphic left and right legs is
the expected three-factor conjugation. -/
@[simp]
theorem LegChange.map.obj.iso.hom
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') (x : F ⊡ G) :
    ((LegChange.map eF eG).obj x).iso.hom =
      eF.inv.app x.fst ≫ x.iso.hom ≫ eG.hom.app x.snd := sorry

/-- The structural inverse map after transport along isomorphic left and right legs is
the reverse three-factor conjugation. -/
@[simp]
theorem LegChange.map.obj.iso.inv
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') (x : F ⊡ G) :
    ((LegChange.map eF eG).obj x).iso.inv =
      eG.inv.app x.snd ≫ x.iso.inv ≫ eF.hom.app x.fst := sorry


end EquivalenceTransportComputations
end Limits.CategoricalPullback
end CategoryTheory
