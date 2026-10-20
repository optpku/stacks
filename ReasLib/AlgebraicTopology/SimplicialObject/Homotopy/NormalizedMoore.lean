/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy.AlternatingFace
public import Mathlib.AlgebraicTopology.DoldKan.Normalized
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 019S

# Normalized Moore complexes and simplicial homotopy

The normalized Moore complex is connected to the alternating-face complex by
the canonical inclusion and retraction. This leaf gives the resulting explicit
transport of a simplicial homotopy, together with its zigzag-relation form.
-/

@[expose] public section

open CategoryTheory
open AlgebraicTopology
open AlgebraicTopology.DoldKan

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {U V : SimplicialObject A} {a b : U ⟶ V}

namespace homotopyRel.normalizedMoore

/-- The normalized Moore complex functor maps simplicial homotopy into chain homotopy. -/
@[stacks 019S "normalized-Moore functor maps homotopy relations"]
instance isMappedBy :
    HomRel.IsMappedBy (homotopyRel A) (normalizedMooreComplex A)
      (homotopic A (ComplexShape.down ℕ)) := sorry

end homotopyRel.normalizedMoore

namespace NormalizedMooreComplex

/-- The normalized-Moore map induced by a simplicial morphism factors through the
alternating-face map using the canonical inclusion and retraction. -/
@[stacks 019S "normalized-Moore factorization through alternating faces"]
theorem map_eq_factorization (f : U ⟶ V) :
    (normalizedMooreComplex A).map f =
      inclusionOfMooreComplexMap U ≫
        ((alternatingFaceMapComplex A).map f ≫ PInftyToNormalizedMooreComplex V) := sorry

end NormalizedMooreComplex

namespace Homotopy

/-- A simplicial homotopy induces an explicit chain homotopy between the maps on normalized
Moore complexes. -/
@[stacks 019S "simplicial homotopy on normalized Moore complexes"]
noncomputable def normalizedMoore (H : Homotopy a b) :
    _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b) :=
  (_root_.Homotopy.ofEq
      (NormalizedMooreComplex.map_eq_factorization a)).trans
    (((H.toChainHomotopy.compRight (PInftyToNormalizedMooreComplex V)).compLeft
        (inclusionOfMooreComplexMap U)).trans
      (_root_.Homotopy.ofEq
        (NormalizedMooreComplex.map_eq_factorization b).symm))

namespace normalizedMoore

/-- The component in degrees `n` and `n + 1` of the normalized-Moore homotopy induced by a
simplicial homotopy. -/
@[stacks 019S "normalized-Moore homotopy component"]
theorem hom (H : Homotopy a b) (n : ℕ) :
    H.normalizedMoore.hom n (n + 1) =
      (inclusionOfMooreComplexMap U).f n ≫ H.toChainHomotopy.hom n (n + 1) ≫
        (PInftyToNormalizedMooreComplex V).f (n + 1) := sorry

end normalizedMoore

end Homotopy

/-- Zigzag-homotopic simplicial morphisms induce the canonical chain-homotopy relation on
normalized Moore complexes. -/
@[stacks 019S "homotopy invariance of normalized Moore complexes"]
theorem Homotopic.normalizedMoore (hab : Homotopic a b) :
    homotopic A (ComplexShape.down ℕ)
      ((normalizedMooreComplex A).map a)
      ((normalizedMooreComplex A).map b) := sorry

end CategoryTheory.SimplicialObject

open CategoryTheory

namespace AlgebraicTopology.normalizedMooreComplex

/-- Canonical lower-camel namespace for the normalized-Moore factorization of a simplicial map. -/
@[stacks 019S "normalized-Moore factorization in the canonical namespace"]
theorem map_eq_factorization {A : Type u} [Category.{v} A] [Abelian A]
    {U V : SimplicialObject A} (f : U ⟶ V) :
    (normalizedMooreComplex A).map f =
      inclusionOfMooreComplexMap U ≫
        ((alternatingFaceMapComplex A).map f ≫ PInftyToNormalizedMooreComplex V) := sorry

end AlgebraicTopology.normalizedMooreComplex
