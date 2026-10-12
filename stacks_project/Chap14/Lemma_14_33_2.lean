/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Endofunctor.ComonadResolution.Augmentation
import StacksCheckRecall

@[expose] public section

/-!
@stack 0G5N

# Lemma 14.33.2

The reusable construction is owned by
`ReasLib.CategoryTheory.Endofunctor.ComonadResolution`. The canonical interface is Mathlib's
`CategoryTheory.Comonad`; the raw bridge remains available for consumers that start from
unbundled counit and comultiplication data.
-/

open Opposite
open CategoryTheory
open CategoryTheory.SimplicialObject
open scoped CategoryTheory.IteratedEndofunctor Simplicial

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {Y : C ⥤ C} (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
variable
  (hσδ₀ : IteratedEndofunctor.degeneracy s 0 0 ≫
    IteratedEndofunctor.face d 0 0 = 𝟙 Y)
  (hσδ₁ : IteratedEndofunctor.degeneracy s 0 0 ≫
    IteratedEndofunctor.face d 0 1 = 𝟙 Y)
  (hσσ : IteratedEndofunctor.degeneracy s 0 0 ≫
      IteratedEndofunctor.degeneracy s 1 0 =
    IteratedEndofunctor.degeneracy s 0 0 ≫
      IteratedEndofunctor.degeneracy s 1 1)

/- Lemma 14.33.2 (1): the raw counit/comultiplication presentation determines the source
simplicial resolution. -/
@[stacks 0G5N "Lemma 14.33.2 (1)"]
#check (EndofunctorResolution.simplicial.resolution d s hσδ₀ hσδ₁ hσσ :
  SimplicialObject (C ⥤ C))

/- Canonical owner: the same construction after bundling the coherence data as a `Comonad`. -/
@[stacks 0G5N "Lemma 14.33.2 (1), canonical comonad resolution"]
#check (Comonad.simplicialResolution : Comonad C → SimplicialObject (C ⥤ C))

@[stacks 0G5N "Lemma 14.33.2 (1), canonical realization witness"]
#check (fun G : Comonad C => G.Realizes G.simplicialResolution)

/- The source's counit-like and comultiplication-like maps are bundled once, then all downstream
results use the canonical comonad API rather than repeatedly carrying three coherence proofs. -/
#check (EndofunctorResolution.toComonad d s hσδ₀ hσδ₁ hσσ : Comonad C)
#check EndofunctorResolution.toComonad.simplicialResolution_eq

/- Raw five-argument realization checks are compatibility bridges, not the reusable owner. -/
#check (EndofunctorResolution.simplicial.resolution.realization d s hσδ₀ hσδ₁ hσσ :
  EndofunctorResolution.Realization d s
    (EndofunctorResolution.simplicial.resolution d s hσδ₀ hσδ₁ hσσ))

/- Lemma 14.33.2 (2): the source counit-like map gives the augmentation. -/
@[stacks 0G5N "Lemma 14.33.2 (2)"]
#check (EndofunctorResolution.Realization.augmentation
    (EndofunctorResolution.simplicial.resolution.realization d s hσδ₀ hσδ₁ hσσ) :
    EndofunctorResolution.simplicial.resolution d s hσδ₀ hσδ₁ hσσ ⟶
    (const (C ⥤ C)).obj (𝟭 C))

/- Canonical owner after bundling the source data as a `Comonad`. -/
@[stacks 0G5N "Lemma 14.33.2 (2), canonical comonad augmentation"]
#check (Comonad.simplicialResolution.augmentation :
  (G : Comonad C) → G.simplicialResolution ⟶ (const (C ⥤ C)).obj (𝟭 C))
#check EndofunctorResolution.toComonad.augmented_eq

end CategoryTheory
