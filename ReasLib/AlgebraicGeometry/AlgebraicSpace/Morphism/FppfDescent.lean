/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth

/-!
# Descent of morphism properties along fppf morphisms and sheaf surjections

If a composite morphism of algebraic spaces is flat, locally of finite type, or
locally of finite presentation, and the first factor is a surjection of sheaves
on `(Sch/S)_fppf`, then the second factor has the same property.

Local finite type, local finite presentation, smoothness, and étaleness descend
under precomposition by a surjective, flat, locally of finite presentation
morphism of algebraic spaces.
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

namespace LocallyOfFinitePresentation

/-- Local finite presentation of morphisms of algebraic spaces descends under
precomposition by a surjective, flat, locally of finite presentation
morphism. -/
instance hasOfPrecompFppf {S : Scheme.{u}} :
    MorphismProperty.HasOfPrecompProperty
      (@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S))
      ((@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S) :
        MorphismProperty (AlgebraicSpace S)) := sorry

/-- In a commutative triangle `f ≫ q = p` of algebraic spaces over `S`, local
finite presentation descends from `p` to `q` when `f` is surjective, flat, and
locally of finite presentation. -/
theorem of_comp_eq_of_fppf {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation p] (hcomm : f ≫ q = p) :
    LocallyOfFinitePresentation q := sorry

end LocallyOfFinitePresentation

namespace LocallyOfFiniteType

/-- Local finite type of morphisms of algebraic spaces descends under
precomposition by a surjective, flat, locally of finite presentation
morphism. -/
instance hasOfPrecompFppf {S : Scheme.{u}} :
    MorphismProperty.HasOfPrecompProperty
      (@LocallyOfFiniteType S : MorphismProperty (AlgebraicSpace S))
      ((@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S) :
        MorphismProperty (AlgebraicSpace S)) := sorry

/-- In a commutative triangle `f ≫ q = p` of algebraic spaces over `S`, local
finite type descends from `p` to `q` when `f` is surjective, flat, and locally
of finite presentation. -/
theorem of_comp_eq_of_fppf {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f]
    [LocallyOfFiniteType p] (hcomm : f ≫ q = p) :
    LocallyOfFiniteType q := sorry

end LocallyOfFiniteType

namespace Smooth

/-- Smoothness of morphisms of algebraic spaces descends under precomposition by
a surjective, flat, locally of finite presentation morphism. -/
instance hasOfPrecompFppf {S : Scheme.{u}} :
    MorphismProperty.HasOfPrecompProperty
      (@Smooth S : MorphismProperty (AlgebraicSpace S))
      ((@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S) :
        MorphismProperty (AlgebraicSpace S)) := sorry

/-- In a commutative triangle `f ≫ q = p` of algebraic spaces over `S`,
smoothness descends from `p` to `q` when `f` is surjective, flat, and locally of
finite presentation. -/
theorem of_comp_eq_of_fppf {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f] [Smooth p]
    (hcomm : f ≫ q = p) : Smooth q := sorry

end Smooth

namespace Etale

/-- Étaleness of morphisms of algebraic spaces descends under precomposition by
a surjective, flat, locally of finite presentation morphism. -/
instance hasOfPrecompFppf {S : Scheme.{u}} :
    MorphismProperty.HasOfPrecompProperty
      (@Etale S : MorphismProperty (AlgebraicSpace S))
      ((@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S) :
        MorphismProperty (AlgebraicSpace S)) := sorry

/-- In a commutative triangle `f ≫ q = p` of algebraic spaces over `S`,
étaleness descends from `p` to `q` when `f` is surjective, flat, and locally of
finite presentation. -/
theorem of_comp_eq_of_fppf {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f] [Etale p]
    (hcomm : f ≫ q = p) : Etale q := sorry

end Etale

end AlgebraicGeometry.AlgebraicSpace
