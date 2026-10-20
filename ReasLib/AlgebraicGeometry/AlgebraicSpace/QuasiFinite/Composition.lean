module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of quasi-finite morphisms of algebraic spaces

Composition preserves quasi-finiteness and the conjunction of local finite type
with chartwise local quasi-finiteness.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Quasi-finite morphisms of algebraic spaces are stable under composition. -/
instance quasiFinite_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@QuasiFinite S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of quasi-finite morphisms of algebraic spaces is
quasi-finite. -/
instance quasiFinite_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiFinite f] [QuasiFinite g] :
    QuasiFinite (f ≫ g) :=
  MorphismProperty.comp_mem (@QuasiFinite S) f g inferInstance inferInstance

/-- Morphisms of algebraic spaces that are locally of finite type and locally
quasi-finite are stable under composition. -/
instance locallyQuasiFinite_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
        MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of morphisms of algebraic spaces that are locally of finite
type and locally quasi-finite has both properties. -/
theorem locallyQuasiFinite_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [LocallyOfFiniteType g] [LocallyQuasiFinite g] :
    LocallyOfFiniteType (f ≫ g) ∧ LocallyQuasiFinite (f ≫ g) :=
  MorphismProperty.comp_mem
    (@LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
      MorphismProperty (AlgebraicSpace S)) f g
    ⟨inferInstance, inferInstance⟩ ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.AlgebraicSpace
