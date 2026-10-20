module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import Mathlib.CategoryTheory.IsomorphismClasses

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh.Derived

/-- For a quasi-compact, quasi-separated, flat morphism of algebraic spaces,
derived module pushforward followed by the derived coherator is naturally isomorphic
to the derived coherator followed by derived quasi-coherent pushforward. -/
theorem pushforwardCoherator_isomorphic {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [Flat f] :
    IsIsomorphic (Modules.moduleDerivedPushforward f ⋙ coherator Y)
      (coherator X ⋙ pushforward f) := sorry

end AlgebraicGeometry.AlgebraicSpace.QCoh.Derived
