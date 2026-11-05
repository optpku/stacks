/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Gluing.OpenFamily.Basis

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived.Gluing

/-
Theorem 20.45.8 (BBD gluing lemma): coherent derived modules on an open cover generating its
pairwise intersections, with vanishing negative self-Ext, admit an ambient realization unique
up to a unique compatible isomorphism. A topological basis is a special case.
-/

@[stacks 0D6C "Theorem 20.45.8 (BBD gluing lemma)"]
#check @OpenFamily.existsUnique

@[stacks 0D6C "BBD gluing realization on an overlap-generating open cover"]
#check @OpenFamily.existsRealization

@[stacks 0D6C "BBD gluing unique compatible isomorphism"]
#check @OpenFamily.existsUniqueIso

@[stacks 0D6C "basiswise BBD gluing lemma"]
#check @OpenFamily.Basis.existsUnique

@[stacks 0D6C "basiswise BBD gluing realization"]
#check @OpenFamily.Basis.existsRealization
@[stacks 0D6C "basiswise BBD gluing unique isomorphism"]
#check @OpenFamily.Basis.existsUniqueIso

end
