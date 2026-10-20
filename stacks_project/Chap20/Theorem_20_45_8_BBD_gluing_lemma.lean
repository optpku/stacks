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
Theorem 20.45.8 (BBD gluing lemma): coherent derived modules on a basis of opens, with vanishing
negative self-Ext, admit an ambient realization unique up to a unique compatible isomorphism.
-/

@[stacks 0D6C "Theorem 20.45.8 (BBD gluing lemma)"]
#check @OpenFamily.Basis.existsUnique

@[stacks 0D6C "basiswise BBD gluing realization"]
#check @OpenFamily.Basis.existsRealization
@[stacks 0D6C "basiswise BBD gluing unique isomorphism"]
#check @OpenFamily.Basis.existsUniqueIso

end
