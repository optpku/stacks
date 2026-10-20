module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSquare
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.StalkFlatness

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A module sheaf is flat over an algebraic space if every étale scheme square realizes it
as a module whose stalks are flat over the target chart's local rings. -/
def FlatOver (F : Modules X) (f : X ⟶ Y) : Prop :=
  ∀ square : EtaleSquare f,
    Scheme.Modules.IsStalkFlatOver
      ((toScheme ((SmallEtale.fromPresentation X).obj square.left)).obj F) square.map.left

/-- Relative flatness can be checked on any pair of representably étale charts and a
commuting scheme morphism, without constructing a geometric square explicitly. -/
theorem flatOver_iff (F : Modules X) (f : X ⟶ Y) :
    FlatOver F f ↔ ∀ (U : site X) (V : site Y) (g : U.left ⟶ V.left),
      yoneda.map g ≫ V.hom = U.hom ≫ f →
        Scheme.Modules.IsStalkFlatOver ((toScheme U).obj F) g.left := sorry

end AlgebraicGeometry.AlgebraicSpace.SmallEtale.Modules
