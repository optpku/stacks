module

public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.Over
public import ReasLib.CategoryTheory.Sites.Simplicial.Homology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Augmented simplicial presheaves

This leaf owns the degree-zero, degree-one, and higher matching maps associated to an
augmentation, together with the induced degree-zero homology comparison.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory

open AlgebraicTopology
open Limits
open Opposite
open SimplicialObject
open scoped Simplicial

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{max w v}]
variable {K : SimplicialObject (Cᵒᵖ ⥤ Type (max w v))}
variable {𝒢 : Cᵒᵖ ⥤ Type (max w v)}

namespace SimplicialPresheaf.Homology

/-- The degree-zero homology map induced by an augmentation of a simplicial presheaf. -/
@[stacks 01GC "augmentation map"]
noncomputable abbrev augmentationMap
    (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type (max w v))) :
    (functor J 0).obj A.left ⟶ J.freeAbelianSheaf A.right :=
  (functor J 0).map A.hom ≫ (constZeroIsoApp J A.right).hom

/-- The augmentation map is homology in degree zero followed by the constant-object natural
isomorphism. -/
@[simp]
theorem augmentationMap_def
    (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type (max w v))) :
    augmentationMap J A =
      (functor J 0).map A.hom ≫ (constZeroIsoApp J A.right).hom := sorry

end SimplicialPresheaf.Homology

namespace SimplicialPresheaf.Homology.CechNerve

/-- Lemma 25.4.2 (1): a locally surjective map of presheaves has acyclic positive-degree
homology in its augmented Cech nerve. -/
@[stacks 01GC "positive degrees"]
theorem succ_isZero
    {ℱ 𝒢 : Cᵒᵖ ⥤ Type (max w v)}
    (φ : ℱ ⟶ 𝒢) [Presheaf.IsLocallySurjective J φ] (n : ℕ) :
    IsZero ((functor J (n + 1)).obj (Arrow.mk φ).cechNerve) := sorry

/-- Lemma 25.4.2 (2): the degree-zero homology map for the augmented Cech nerve of a locally
surjective presheaf map is an isomorphism. -/
@[stacks 01GC "degree zero"]
theorem augmentationMap_isIso
    {ℱ 𝒢 : Cᵒᵖ ⥤ Type (max w v)}
    (φ : ℱ ⟶ 𝒢) [Presheaf.IsLocallySurjective J φ] :
    IsIso (augmentationMap J (Arrow.mk φ).augmentedCechNerve) := sorry

end SimplicialPresheaf.Homology.CechNerve

namespace SimplicialPresheaf.Homology.Comparison

/-- Lemma 25.4.3: a degreewise locally surjective comparison between coskeletal simplicial
presheaves induces an isomorphism on homology. -/
@[stacks 01GD]
theorem ofCoskUnit
    {L K : SimplicialObject (Cᵒᵖ ⥤ Type (max w v))}
    (f : L ⟶ K) (n i : ℕ)
    (hbelow : ∀ j < n, IsIso (f.app (op ⦋j⦌)))
    (hSurj : Presheaf.IsLocallySurjective J (f.app (op ⦋n⦌)))
    (hL : IsIso ((coskAdj n).unit.app L))
    (hK : IsIso ((coskAdj n).unit.app K)) :
    IsIso ((functor J i).map f) := sorry

/-- A coskeletal formulation of the homology-isomorphism criterion for simplicial
presheaves. -/
theorem ofCoskeletal
    {L K : SimplicialObject (Cᵒᵖ ⥤ Type (max w v))}
    (f : L ⟶ K) (n i : ℕ)
    (hbelow : ∀ j < n, IsIso (f.app (op ⦋j⦌)))
    (hSurj : Presheaf.IsLocallySurjective J (f.app (op ⦋n⦌)))
    (hL : L.IsCoskeletal n) (hK : K.IsCoskeletal n) :
    IsIso ((functor J i).map f) := sorry

end SimplicialPresheaf.Homology.Comparison

end CategoryTheory
