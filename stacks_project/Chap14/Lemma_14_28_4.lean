/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.Opposite
import StacksCheckRecall

/-!
@stack 019Y

# Functoriality of simplicial and cosimplicial homotopy

The functoriality and opposite-variance APIs are owned by the corresponding homotopy relation
namespaces in `ReasLib`.
-/

@[expose] public section

open CategoryTheory

universe u v u' v'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]

section Covariant

variable {U V : SimplicialObject C} {a b : U ⟶ V}
variable (hS : SimplicialObject.Homotopic a b) (F : C ⥤ D)

/- Lemma 14.28.4 (1): covariant functors preserve simplicial homotopy. -/
@[stacks 019Y "Lemma 14.28.4 (1)"]
#check (hS.whiskerRight F :
  SimplicialObject.Homotopic
    (Functor.whiskerRight a F) (Functor.whiskerRight b F))

variable {U' V' : CosimplicialObject C} {a' b' : U' ⟶ V'}
variable (hC : CosimplicialObject.DeltaOneHomotopic a' b')

/- Lemma 14.28.4 (2): covariant functors preserve product-free cosimplicial `Δ[1]`-homotopy. -/
@[stacks 019Y "Lemma 14.28.4 (2)"]
#check (hC.whiskerRight F :
  CosimplicialObject.DeltaOneHomotopic
    (Functor.whiskerRight a' F) (Functor.whiskerRight b' F))

end Covariant

section Contravariant

variable {X Y : SimplicialObject D} {f g : X ⟶ Y}
variable (hS : SimplicialObject.Homotopic f g) (F : D ⥤ Cᵒᵖ)

/- Lemma 14.28.4 (3): contravariant functors send simplicial homotopy to product-free
cosimplicial `Δ[1]`-homotopy. -/
@[stacks 019Y "Lemma 14.28.4 (3)"]
#check (hS.contravariantMap F :
  CosimplicialObject.DeltaOneHomotopic
    (NatTrans.unop (Functor.whiskerRight f F))
    (NatTrans.unop (Functor.whiskerRight g F)))

variable {U V : CosimplicialObject C} {a b : U ⟶ V}
variable (hC : CosimplicialObject.DeltaOneHomotopic a b) (G : Cᵒᵖ ⥤ D)

/- Lemma 14.28.4 (4): contravariant functors send product-free cosimplicial `Δ[1]`-homotopy to
simplicial homotopy. -/
@[stacks 019Y "Lemma 14.28.4 (4)"]
#check (hC.contravariantMap G :
  SimplicialObject.Homotopic
    (Functor.whiskerRight (NatTrans.op a) G)
    (Functor.whiskerRight (NatTrans.op b) G))

end Contravariant

end CategoryTheory
