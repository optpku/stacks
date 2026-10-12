/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Descent of flatness and finiteness along fppf sheaf surjections

If a composite morphism of algebraic spaces is flat, locally of finite type, or
locally of finite presentation, and the first factor is a surjection of sheaves
on `(Sch/S)_fppf`, then the second factor has the same property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Flat

/-- If `f ≫ g` is a flat morphism of algebraic spaces over `S` and `f` is a
surjection of sheaves on `(Sch/S)_fppf`, then `g` is flat. -/
theorem of_comp_of_isLocallySurjective {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat (f ≫ g)]
    [Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) f] :
    Flat g := sorry

end Flat

namespace LocallyOfFiniteType

/-- If `f ≫ g` is locally of finite type as a morphism of algebraic spaces over
`S` and `f` is a surjection of sheaves on `(Sch/S)_fppf`, then `g` is locally of
finite type. -/
theorem of_comp_of_isLocallySurjective {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType (f ≫ g)]
    [Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) f] :
    LocallyOfFiniteType g := sorry

end LocallyOfFiniteType

namespace LocallyOfFinitePresentation

/-- If `f ≫ g` is locally of finite presentation as a morphism of algebraic
spaces over `S` and `f` is a surjection of sheaves on `(Sch/S)_fppf`, then `g` is
locally of finite presentation. -/
theorem of_comp_of_isLocallySurjective {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ g)]
    [Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) f] :
    LocallyOfFinitePresentation g := sorry

end LocallyOfFinitePresentation

end AlgebraicGeometry.AlgebraicSpace
