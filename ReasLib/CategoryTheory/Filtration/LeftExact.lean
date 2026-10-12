/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Preadditive.LeftExact
public import ReasLib.CategoryTheory.Filtration.Map.Preadditive

@[expose] public section

/-!
# Left-Exact Functors on Finite Filtered Objects

This is the left-exact front end for `Filtration.Map`. Mathlib derives preservation of
monomorphisms and zero morphisms from finite-limit preservation, while the neutral functor
support module supplies the corresponding additivity instance.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.LeftExact

open Limits

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

section ReusableInference

variable [HasZeroMorphisms C] [HasZeroMorphisms D]
  [HasZeroObject C] [HasZeroObject D]
  [Preadditive C] [Preadditive D] [HasBinaryBiproducts C]
variable (T : C ⥤ₗ D)

#synth T.obj.PreservesMonomorphisms
#synth T.obj.PreservesZeroMorphisms
#synth T.obj.Additive
#synth (FilteredObject.mapFunctor T.obj).PreservesZeroMorphisms
#synth (FilteredObject.Finite.mapFunctor T.obj).Additive

end ReusableInference

end CategoryTheory.FilteredObject.LeftExact
