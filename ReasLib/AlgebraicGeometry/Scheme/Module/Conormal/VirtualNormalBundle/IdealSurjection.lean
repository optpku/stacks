module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.VirtualNormalBundle
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback

/-!
# Virtual normal bundles from ideal-sheaf quotients

An invertible module whose dual surjects onto the pulled-back ideal sheaf of a closed
immersion determines a rank-one virtual normal bundle.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

/-- Composing an epimorphism onto the pulled-back ideal sheaf with the canonical conormal
comparison remains an epimorphism. -/
theorem idealSurjectionMap_epi {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (N : D.Modules)
    (sigma : Scheme.Modules.dual N ⟶
      (Scheme.Modules.pullback i).obj (RingedSpace.Hom.kernelIdealSheaf i.toShHom))
    [Epi sigma] : Epi (sigma ≫ Conormal.pullbackIdealComparison i) := sorry

/-- An invertible module and an ideal-sheaf quotient determine the associated rank-one
virtual normal bundle. -/
noncomputable def ofIdealSurjection {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (N : D.Modules) [Scheme.Modules.Invertible N]
    (sigma : Scheme.Modules.dual N ⟶
      (Scheme.Modules.pullback i).obj (RingedSpace.Hom.kernelIdealSheaf i.toShHom))
    [Epi sigma] : VirtualNormalBundle i :=
  ofSurjection i N
    (@Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank D 1 N
      (Scheme.Modules.isFiniteLocallyFreeOfRankOne_of_invertible N))
    (sigma ≫ Conormal.pullbackIdealComparison i)
    (idealSurjectionMap_epi i N sigma)

/-- The virtual normal bundle constructed from an ideal-sheaf quotient retains the given
module. -/
theorem ofIdealSurjection_module {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (N : D.Modules) [Scheme.Modules.Invertible N]
    (sigma : Scheme.Modules.dual N ⟶
      (Scheme.Modules.pullback i).obj (RingedSpace.Hom.kernelIdealSheaf i.toShHom))
    [Epi sigma] : (ofIdealSurjection i N sigma).module = N := sorry

/-- The quotient map of the virtual normal bundle constructed from an ideal-sheaf quotient
is the given quotient followed by the conormal comparison. -/
theorem ofIdealSurjection_map {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (N : D.Modules) [Scheme.Modules.Invertible N]
    (sigma : Scheme.Modules.dual N ⟶
      (Scheme.Modules.pullback i).obj (RingedSpace.Hom.kernelIdealSheaf i.toShHom))
    [Epi sigma] :
    (ofIdealSurjection i N sigma).map = sigma ≫ Conormal.pullbackIdealComparison i := sorry

end AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
