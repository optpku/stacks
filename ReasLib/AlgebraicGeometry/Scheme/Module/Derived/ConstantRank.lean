module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FiberEulerCharacteristic.Pullback

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- A derived module has constant virtual rank `r` when the Euler characteristic of each
derived fiber is `r`. -/
def IsConstantRank {X : Scheme.{u}}
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (r : ℤ) : Prop :=
  fiberEulerChar E = fun _ ↦ r

/-- Constant virtual rank is equivalent to pointwise equality of the derived-fiber Euler
characteristic with the specified integer. -/
theorem isConstantRank_iff {X : Scheme.{u}}
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (r : ℤ) :
    IsConstantRank E r ↔ ∀ x : X, fiberEulerChar E x = r := sorry

namespace IsConstantRank

/-- Constant virtual rank is preserved under isomorphisms of derived modules. -/
theorem of_iso {X : Scheme.{u}}
    {E F : RingedSpace.ModuleDerived X.toRingedSpace} {r : ℤ}
    (hE : IsConstantRank E r) (e : E ≅ F) : IsConstantRank F r := sorry

/-- Derived pullback preserves the constant virtual rank of a pseudo-coherent module. -/
theorem pullback {X Y : Scheme.{u}}
    {E : RingedSpace.ModuleDerived X.toRingedSpace} {r : ℤ}
    (hE : IsConstantRank E r) (f : Y ⟶ X)
    (hPseudo : RingedSpace.ModuleDerived.IsPseudoCoherent E) :
    IsConstantRank ((RingedSpace.modulePullbackDerived f.toShHom).obj E) r := sorry

end IsConstantRank

end AlgebraicGeometry.Scheme.ModuleDerived
