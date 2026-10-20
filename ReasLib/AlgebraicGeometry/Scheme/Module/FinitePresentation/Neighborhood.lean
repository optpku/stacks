module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Stalk.Restriction

/-!
# Extending stalk morphisms to neighborhoods

A morphism from the stalk of a finitely presented module sheaf is induced by a morphism on
some open neighborhood of the point.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsFinitePresentation

/-- A morphism from the stalk of a finitely presented module sheaf to the stalk of any module
sheaf extends to a morphism between their restrictions on some open neighborhood. -/
theorem existsNeighborhood_restrictHom_of_stalkHom
    {X : Scheme.{u}} {G F : X.Modules} [G.IsFinitePresentation]
    (x : X) (ψ : RingedSpace.stalkModuleCat G x ⟶ RingedSpace.stalkModuleCat F x) :
    ∃ (U : X.Opens) (hxU : x ∈ U)
      (φ : (restrictFunctor U.ι).obj G ⟶ (restrictFunctor U.ι).obj F),
      stalkAddHomOfRestrictHom x U hxU φ =
        (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map ψ := sorry

end AlgebraicGeometry.Scheme.Modules.IsFinitePresentation
