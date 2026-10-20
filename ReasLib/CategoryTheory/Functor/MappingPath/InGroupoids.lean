module

public import ReasLib.CategoryTheory.Functor.MappingPath
public import ReasLib.CategoryTheory.Fibered.InGroupoids

/-!
# Mapping paths in groupoids

The groupoid-fibration property of a mapping-path projection is optional
fibered-category infrastructure. It is kept separate from the ordinary
categorical mapping-path construction.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

namespace MappingPath

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]

/-- For groupoids `C` and `D`, the mapping-path projection is fibred in groupoids.

Proof strategy: lift a base arrow by composing the stored comparison isomorphism with its inverse.
The source and mapping-path categories are groupoids, so every total morphism is cartesian. -/
instance projectionInGroupoids
    (F : C ⥤ D) [IsGroupoid C] [IsGroupoid D] :
    Functor.IsFibered.InGroupoids (projection F) := sorry

end MappingPath

end Functor

end CategoryTheory
