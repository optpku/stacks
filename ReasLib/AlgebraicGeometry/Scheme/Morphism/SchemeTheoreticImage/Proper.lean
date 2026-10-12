/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper

/-!
# Proper scheme-theoretic images

This file relates universal closedness to the canonical factorization through a
scheme-theoretic image.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- In a commutative triangle whose composite is universally closed and whose second
map is separated and locally of finite type, the canonical map to the scheme-theoretic
image is surjective. -/
theorem toImage_surjective_of_universallyClosed {X Y S : Scheme.{u}}
    (h : X ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (hcomm : h ≫ g = f)
    [UniversallyClosed f] [IsSeparated g] [LocallyOfFiniteType g] :
    Surjective h.toImage := sorry

/-- In a commutative triangle whose composite is universally closed and whose second
map is separated and locally of finite type, the scheme-theoretic image is proper
over the base. -/
theorem imageι_comp_isProper_of_universallyClosed {X Y S : Scheme.{u}}
    (h : X ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (hcomm : h ≫ g = f)
    [UniversallyClosed f] [IsSeparated g] [LocallyOfFiniteType g] :
    IsProper (h.imageι ≫ g) := sorry

end AlgebraicGeometry.Scheme.Hom
