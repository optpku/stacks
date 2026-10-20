module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent.Forget

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- The forgetful functor from equivariant quasi-coherent modules to quasi-coherent
modules on the object scheme. -/
#check (AlgebraicGeometry.GroupoidScheme.QCoh.forget :
  ∀ {S : Scheme.{u}}, (G : GroupoidScheme S) →
    G.QCoh ⥤ Scheme.QCoh G.U.left)
