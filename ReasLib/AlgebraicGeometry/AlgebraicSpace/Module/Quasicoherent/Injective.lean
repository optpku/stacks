module

public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

/-- Pushforward along a flat, quasi-compact, and quasi-separated morphism of
algebraic spaces sends injective quasi-coherent modules to injective objects. -/
theorem pushforward.injective_obj
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [Flat f]
    (J : QCoh X) (hJ : Injective J) :
    Injective ((pushforward f).obj J) :=
  sorry

/-- Quasi-coherent pushforward along a flat, quasi-compact, and quasi-separated
morphism of algebraic spaces preserves injective objects. -/
instance pushforward.preservesInjectiveObjects
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [Flat f] :
    (pushforward f).PreservesInjectiveObjects where
  injective_obj {J} hJ := pushforward.injective_obj f J hJ

end AlgebraicGeometry.AlgebraicSpace.QCoh
