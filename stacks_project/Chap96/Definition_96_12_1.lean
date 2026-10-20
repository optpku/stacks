module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.LocallyQuasicoherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver

universe u

/- Definition 96.12.1: let `p : X ⟶ (Sch/S)_fppf` be a category fibred in
groupoids. Let `F` be a presheaf of `𝒪_X`-modules. We say `F` is locally
quasi-coherent if `F` is a sheaf for the étale topology and for every object
`x` of `X` the restriction `x* F|_{U_étale}` is a quasi-coherent sheaf.
Here `U = p(x)`. -/
@[stacks 06WJ] #check (AlgebraicGeometry.GroupoidsOver.IsLocallyQuasicoherent :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.GroupoidsOver S},
    PresheafOfModules.{u} (AlgebraicGeometry.GroupoidsOver.structureSheaf X).obj → Prop)
