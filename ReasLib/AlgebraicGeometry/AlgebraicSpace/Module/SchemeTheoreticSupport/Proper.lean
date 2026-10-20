module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTheoreticSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support.Closed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubset.Proper

/-!
# Properness of module support over a base

For a locally of finite type morphism of algebraic spaces and a finite-type
quasi-coherent module, properness of the closed support, properness of the
scheme-theoretic support, and descent from a proper closed subspace are
equivalent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Properness of the closed support of a finite-type quasi-coherent module over
a base is equivalent to properness of its scheme-theoretic support and to
descent from a finite-type quasi-coherent module on a proper closed subspace. -/
theorem closedSupport_isProperOver_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] :
    List.TFAE [
      ClosedSubset.ProperOver f (closedSupport F),
      Proper ((schemeTheoreticSupport F).ι ≫ f),
      ∃ (Z : ClosedSubspace X) (G : Z.X.Modules),
        G.IsFiniteType ∧ G.IsQuasicoherent ∧ Proper (Z.ι ≫ f) ∧
          Nonempty ((pushforward Z.ι).obj G ≅ F)] :=
  sorry

/-- The closed support of a finite-type quasi-coherent module is proper over a
base if and only if the scheme-theoretic support is proper over that base. -/
theorem closedSupport_isProperOver_iff_schemeTheoreticSupport
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    ClosedSubset.ProperOver f (closedSupport F) ↔
      Proper ((schemeTheoreticSupport F).ι ≫ f) :=
  (closedSupport_isProperOver_tfae f F).out 0 1

/-- The closed support of a finite-type quasi-coherent module is proper over a
base if and only if the module is the pushforward of a finite-type
quasi-coherent module from a closed subspace proper over that base. -/
theorem closedSupport_isProperOver_iff_exists_pushforward
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    ClosedSubset.ProperOver f (closedSupport F) ↔
      ∃ (Z : ClosedSubspace X) (G : Z.X.Modules),
        G.IsFiniteType ∧ G.IsQuasicoherent ∧ Proper (Z.ι ≫ f) ∧
          Nonempty ((pushforward Z.ι).obj G ≅ F) :=
  (closedSupport_isProperOver_tfae f F).out 0 2

/-- The scheme-theoretic support of a finite-type quasi-coherent module is proper
over a base if and only if the module is the pushforward of a finite-type
quasi-coherent module from a closed subspace proper over that base. -/
theorem schemeTheoreticSupport_isProper_iff_exists_pushforward
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    Proper ((schemeTheoreticSupport F).ι ≫ f) ↔
      ∃ (Z : ClosedSubspace X) (G : Z.X.Modules),
        G.IsFiniteType ∧ G.IsQuasicoherent ∧ Proper (Z.ι ≫ f) ∧
          Nonempty ((pushforward Z.ι).obj G ≅ F) :=
  (closedSupport_isProperOver_tfae f F).out 1 2

end AlgebraicGeometry.AlgebraicSpace.Modules
