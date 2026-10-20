module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Locus

/-!
# Relative flatness loci and arbitrary base change

For composable morphisms of algebraic spaces, a finitely presented module flat
over the final base has an open relative flatness locus over the intermediate
space, compatible with arbitrary base change, under the corresponding finite
presentation and finite type assumptions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- For composable morphisms of algebraic spaces, the relative flatness locus of a
finitely presented module is open if the source is locally finitely presented over
the final base, the module is flat over that base, and the intermediate space is
locally of finite type over it. -/
@[stacks 05X2]
theorem isOpen_flatOverAt_of_flatOver {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (h : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ h)]
    [LocallyOfFiniteType h] (F : X.Modules) [F.IsFinitePresentation]
    (h_flat : flatOver F (f ≫ h)) : IsOpen (flatOverLocus F f) :=
  sorry

/-- For a finitely presented module flat over the final base of two composable
morphisms, its relative flatness locus over the intermediate space commutes with
arbitrary base change when the source is locally finitely presented over the
final base and the intermediate space is locally of finite type over it. -/
@[stacks 05X2]
theorem flatOverLocus_baseChange_eq_preimage {S : Scheme.{u}}
    {X Y Z Z' : AlgebraicSpace S} (f : X ⟶ Y) (h : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ h)] [LocallyOfFiniteType h]
    (F : X.Modules) [F.IsFinitePresentation] (h_flat : flatOver F (f ≫ h)) :
    flatOverLocus ((pullback (pullback.fst (f ≫ h) g)).obj F)
        (overBaseChange f h g) =
      Points.map (pullback.fst (f ≫ h) g) ⁻¹' flatOverLocus F f :=
  sorry

/-- A point of `Points (pullback (f ≫ h) g)` lies in the relative-flatness locus
of the pulled-back module over `overBaseChange f h g` if and only if its image
under `Points.map (pullback.fst (f ≫ h) g)` lies in `flatOverLocus F f`. -/
theorem mem_flatOverLocus_baseChange_eq_preimage {S : Scheme.{u}}
    {X Y Z Z' : AlgebraicSpace S} (f : X ⟶ Y) (h : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ h)] [LocallyOfFiniteType h]
    (F : X.Modules) [F.IsFinitePresentation] (h_flat : flatOver F (f ≫ h))
    (x' : Points (Limits.pullback (f ≫ h) g)) :
    x' ∈ flatOverLocus ((pullback (pullback.fst (f ≫ h) g)).obj F)
          (overBaseChange f h g) ↔
      Points.map (pullback.fst (f ≫ h) g) x' ∈ flatOverLocus F f := by
  rw [flatOverLocus_baseChange_eq_preimage f h g F h_flat]
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
