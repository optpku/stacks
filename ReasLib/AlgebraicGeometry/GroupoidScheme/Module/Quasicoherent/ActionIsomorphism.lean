module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme.QCoh

/-- The action morphism of an equivariant quasi-coherent module on a groupoid scheme is
an isomorphism. -/
theorem action_isIso {S : Scheme.{u}} {G : GroupoidScheme S} (A : G.QCoh) :
    IsIso A.action := sorry

end AlgebraicGeometry.GroupoidScheme.QCoh
