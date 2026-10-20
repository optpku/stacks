module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Stalk.Restriction
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- 75.10.0.1: for an étale morphism `j : U ⟶ X` of algebraic spaces over `S`, a sheaf of
`𝒪_X`-modules `F`, and a geometric point `ubar` of `U`, the stalk of the étale restriction
`restrict F j` at `ubar` is canonically identified with the stalk of `F` at `ubar.map j`. -/
@[stacks 08GT] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.restrictStalkIso :
    ∀ {S : Scheme.{u}} {U X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
      (F : X.Modules) (ubar : GeometricPoint U),
      stalkModuleCat ubar (restrict F j) ≅
        (ModuleCat.restrictScalars (etaleLocalRingHom j ubar)).obj
          (stalkModuleCat (ubar.map j) F))
