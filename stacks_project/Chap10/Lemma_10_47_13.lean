/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.GeometricallyIrreducible
public import ReasLib.FieldTheory.SeparableClosure.FiniteType
import StacksCheckRecall

@[expose] public section

/-!
# Relative separable closures

Lemma 10.47.13 has two independent reusable consequences: the extension over its relative
separable closure is geometrically irreducible, and essential finite type makes that closure
finite-dimensional.  Neither fact is a global instance, because both require a specific chosen
field extension.

@stack 037Q
-/

/- Lemma 10.47.13 (Tag 037Q): geometric irreducibility over the relative separable closure. -/
@[stacks 037Q]
#check @AlgebraicGeometry.FieldExtension.GeometricallyIrreducible.of_separableClosure

/- Lemma 10.47.13 (Tag 037Q): finite-dimensionality of the relative separable closure. -/
@[stacks 037Q]
#check @FieldExtension.SeparableClosure.finiteDimensional_of_essFiniteType

end
