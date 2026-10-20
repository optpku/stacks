module

public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Presheaf
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Singleton

/-!
# Presheaf comparisons for singleton formal coproduct replacements

This module records the map between the presheaves represented by a formal coproduct and a chosen
singleton-coproduct replacement.  It depends only on the generic presheaf realization of formal
coproducts.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory

namespace Limits
namespace FormalCoproduct

variable {C : Type u} [Category.{v} C]

/-- The presheaf map induced by the canonical map to a chosen singleton-coproduct replacement. -/
def coproductSingletonComparison (K L : FormalCoproduct.{w} C) [HasCoproduct K.obj]
    (hL : coproductSingleton K = L) :
    toPresheaf.obj K ⟶ toPresheaf.obj L :=
  toPresheaf.map (toCoproductSingletonOfEq K L hL)

/-- The singleton-coproduct presheaf comparison is induced by the transported canonical map of
formal coproducts. -/
@[simp] theorem coproductSingletonComparison_def (K L : FormalCoproduct.{w} C)
    [HasCoproduct K.obj] (hL : coproductSingleton K = L) :
    coproductSingletonComparison K L hL =
      toPresheaf.map (toCoproductSingletonOfEq K L hL) := sorry

/-- On a canonical presheaf summand, the singleton-coproduct comparison is induced by the
corresponding component of the transported formal-coproduct map. -/
@[simp] theorem coproductSingletonComparison_objMk (K L : FormalCoproduct.{w} C)
    [HasCoproduct K.obj] (hL : coproductSingleton K = L) (X : Cᵒᵖ)
    (i : K.I) (g : X.unop ⟶ K.obj i) :
    (coproductSingletonComparison K L hL).app X (K.toPresheafObjMk X i g) =
      L.toPresheafObjMk X ((toCoproductSingletonOfEq K L hL).f i)
        (g ≫ (toCoproductSingletonOfEq K L hL).φ i) := sorry

end FormalCoproduct
end Limits

end CategoryTheory
