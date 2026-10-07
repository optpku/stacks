module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.Monoidal
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.18.4

The reusable owner is the strong monoidal structure on derived pullback.  Its tensor comparison
is exposed first as an isomorphism of bifunctors, with pointwise isomorphism and morphism views.
The construction descends the ordinary pullback tensorator through K-flat complexes with flat
terms.
-/

/- Lemma 21.18.4 (07A4): in the commutative ringed-site presentation of a morphism of ringed
topoi, derived pullback carries a derived tensor product canonically to the derived tensor product
of the pullbacks. -/
@[stacks 07A4 "canonical derived pullback tensor comparison"]
#check @RingedSite.Hom.modulePullbackDerived.TensorPreservation.natIso

#check @RingedSite.Hom.modulePullbackDerived.TensorPreservation.iso
