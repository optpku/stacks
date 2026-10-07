module

import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent.Pullback
import StacksCheckRecall

universe u

open AlgebraicGeometry CategoryTheory

variable {S : Scheme.{u}} {G H : GroupoidScheme S} (f : GroupoidScheme.Hom G H)

/- Lemma 39.14.3: a morphism `f : GroupoidScheme.Hom G H` of groupoid schemes over `S` induces the
pullback functor `(F, α) ↦ (f⁎F, f⁎α)` from equivariant quasi-coherent modules on
`H` to equivariant quasi-coherent modules on `G`. -/
@[stacks 03LJ] #check
  (AlgebraicGeometry.GroupoidScheme.QCoh.pullback f : H.QCoh ⥤ G.QCoh)

/- Companion checks: `GroupoidScheme.QCoh.pullback f` is built from the concrete object
and morphism formulas `GroupoidScheme.QCoh.pullbackObj f` and
`GroupoidScheme.QCoh.pullbackMap f`. -/
#check GroupoidScheme.QCoh.pullbackObj
#check GroupoidScheme.QCoh.pullbackMap
