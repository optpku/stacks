module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RelativeRestriction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Local
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent
public import ReasLib.RingTheory.RingHom.Perfect.TorDimension

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.PseudoCoherent

/-- For a pseudo-coherent morphism of schemes, perfectness, local finite Tor dimension of
the derived structure sheaf over the inverse-image structure sheaf, and finite Tor dimension
of every stalk map are equivalent. -/
theorem perfect_tfae {X S : Scheme.{u}} (f : X ⟶ S) [PseudoCoherent f] :
    List.TFAE [LocallyOfType RingHom.IsPerfectRingMap f,
      RingedSpace.ModuleDerived.LocallyHasFiniteTorDimension
        ((RingedSpace.ModuleDerived.relativeRestriction f.toShHom).obj
          (Scheme.DerivedQCoh.structureSheaf X).obj),
      ∀ x : X, (f.stalkMap x).hom.HasFiniteTorDimension] := sorry

end AlgebraicGeometry.PseudoCoherent
