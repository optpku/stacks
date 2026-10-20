module

public import ReasLib.AlgebraicGeometry.RingedSite.LocalHom.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 18.40.10 (04IG): local morphisms of commutative ringed-site presentations are closed
under composition. -/
@[stacks 04IG]
#check @RingedSite.Hom.IsLocal.comp
