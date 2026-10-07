module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Gluing.OpenFamily.Finite

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived.Gluing

/-
Lemma 20.45.6: an open-family gluing datum on a finite cover has an ambient realization, unique
up to a unique compatible isomorphism, under overlap generation and negative self-Ext vanishing.
The finite index type is universe-polymorphic and carries no unnecessary ordering.
-/

@[stacks 0D6A "Lemma 20.45.6: derived gluing over a finite open cover"]
#check @OpenFamily.FiniteCover.existsUnique

@[stacks 0D6A "finite-cover derived realization"]
#check @OpenFamily.FiniteCover.existsRealization

end
