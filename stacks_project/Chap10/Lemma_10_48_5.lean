module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Affine.Connected
import StacksCheckRecall

@[expose] public section

/-!
# Closure Properties of Geometrically Connected Affine Algebras

Lemma 10.48.5 is a canonical recall.  The reusable owner uses mathlib's
canonical `GeometricallyConnected` class, whose underlying proposition is the
source-facing `geometrically (ConnectedSpace ·)` predicate.  Its categorical
filtered-or-empty colimit form subsumes the ordered directed-system statement.

@stack 037V
-/

/- Lemma 10.48.5 (Tag 037V), canonical geometric-connectedness predicate and
its source-facing presentation. -/
@[stacks 037V]
#check @AlgebraicGeometry.GeometricallyConnected
#check @AlgebraicGeometry.GeometricallyConnected.eq_geometrically

/- Lemma 10.48.5 (1) (Tag 037V): geometric connectedness descends along an
injective affine algebra morphism, in particular along subalgebra inclusions. -/
@[stacks 037V]
#check @AlgebraicGeometry.SchemeOverField.GeometricallyConnected.of_injective
#check @AlgebraicGeometry.SchemeOverField.GeometricallyConnected.of_subalgebra
#check @AlgebraicGeometry.SchemeOverField.GeometricallyConnected.instSubalgebra

/- Lemma 10.48.5 (2) (Tag 037V): it is enough to test geometric connectedness
on finitely generated subalgebras. -/
@[stacks 037V]
#check @AlgebraicGeometry.SchemeOverField.GeometricallyConnected.of_forall_fg

/- Lemma 10.48.5 (3) (Tag 037V): filtered-or-empty colimits preserve geometric
connectedness. -/
@[stacks 037V]
#check @AlgebraicGeometry.SchemeOverField.GeometricallyConnected.of_filteredColimit
