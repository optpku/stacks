/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-!
# Descent of separatedness

Separation properties descend through surjective universally closed morphisms of schemes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Quasi-separatedness of a composite descends to the right factor when the left factor is
surjective and universally closed. -/
theorem QuasiSeparated.of_comp_surjective_universallyClosed
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [Surjective f] [UniversallyClosed f] [QuasiSeparated (f ≫ g)] :
    QuasiSeparated g := sorry

/-- Separatedness of a composite descends to the right factor when the left factor is
surjective and universally closed. -/
theorem IsSeparated.of_comp_surjective_universallyClosed
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [Surjective f] [UniversallyClosed f] [IsSeparated (f ≫ g)] :
    IsSeparated g := sorry

namespace Scheme

/-- A scheme dominated by a quasi-separated scheme through a surjective universally closed
morphism is quasi-separated. -/
theorem quasiSeparatedSpace_of_surjective_universallyClosed
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Surjective f] [UniversallyClosed f] [QuasiSeparatedSpace X] :
    QuasiSeparatedSpace Y := sorry

/-- A scheme dominated by a separated scheme through a surjective universally closed morphism
is separated. -/
theorem isSeparated_of_surjective_universallyClosed
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Surjective f] [UniversallyClosed f] [X.IsSeparated] :
    Y.IsSeparated := sorry

end Scheme
end AlgebraicGeometry
