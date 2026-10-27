/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SchemeMorphism.ExactSequence
import StacksCheckRecall

/-! # The canonical infinitesimal exact sequence of a morphism of schemes -/

open CategoryTheory AlgebraicGeometry

universe u
variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
variable (hf : f ≫ hY = hX)

/- Lemma 93.10.3 (1) -/
@[stacks 0E3V] #check (FlatSchemeMorphismCat.infToProdInf_injective Λ k f hX hY hf :
  Function.Injective (FlatSchemeMorphismCat.infToProdInf Λ k f hX hY hf))

/- Lemma 93.10.3 (2) -/
@[stacks 0E3V] #check (FlatSchemeMorphismCat.exact_inf_prodInf_der Λ k f hX hY hf :
  Function.Exact (FlatSchemeMorphismCat.infToProdInf Λ k f hX hY hf)
    (FlatSchemeMorphismCat.prodInfToDer Λ k f hX hY hf))

/- Lemma 93.10.3 (3) -/
@[stacks 0E3V] #check (FlatSchemeMorphismCat.exact_prodInf_der_tangent Λ k f hX hY hf :
  Function.Exact (FlatSchemeMorphismCat.prodInfToDer Λ k f hX hY hf)
    (FlatSchemeMorphismCat.derToTangent Λ k f hX hY hf))

/- Lemma 93.10.3 (4) -/
@[stacks 0E3V] #check (FlatSchemeMorphismCat.exact_der_tangent_prodTangent Λ k f hX hY hf :
  Function.Exact (FlatSchemeMorphismCat.derToTangent Λ k f hX hY hf)
    (FlatSchemeMorphismCat.tangentToProdTangent Λ k f hX hY hf))

/- Lemma 93.10.3 (5) -/
@[stacks 0E3V] #check (FlatSchemeMorphismCat.exact_prodTangent_ext Λ k f hX hY hf :
  Function.Exact (FlatSchemeMorphismCat.tangentToProdTangent Λ k f hX hY hf)
    (FlatSchemeMorphismCat.prodTangentToExt Λ k f hX hY hf))
