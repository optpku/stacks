/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.ExtraDegeneracy
public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.LastExtraDegeneracy.Homotopy
public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.UnderlyingHomotopyEquivalence.Functor

/-!
# Alternating-face complexes of augmented simplicial objects

The canonical alternating-face augmentation factors through the alternating-face image of the
simplicial augmentation.  This file packages that factorization, homotopy-equivalence and
underlying-functor criteria, and the reusable extra-degeneracy specialization.

@stack 08ND
-/

@[expose] public section

open CategoryTheory HomologicalComplex
open AlgebraicTopology

universe u v w x y

namespace AlgebraicTopology.AlternatingFaceMapComplex

section Factorization

variable {A : Type u} [Category.{v} A] [Preadditive A] [Limits.HasZeroObject A]

/-- The alternating-face image of an augmented simplicial map followed by the constant
augmentation is the canonical augmentation of the original object. -/
@[reassoc, stacks 019T "factorization of the alternating-face augmentation"]
theorem map_hom_comp_ε_const (X : SimplicialObject.Augmented A) :
    (alternatingFaceMapComplex A).map X.hom ≫
        ε.app (SimplicialObject.Augmented.const.obj X.right) =
      ε.app X := sorry

end Factorization

section QuasiIso

variable {A : Type u} [Category.{v} A] [Preadditive A] [Limits.HasZeroObject A]
  [CategoryWithHomology A]

/-- The canonical alternating-face augmentation of a constant simplicial object is a
quasi-isomorphism. -/
@[stacks 019T "constant alternating-face augmentation quasi-isomorphism"]
instance const_ε_quasiIso (Z : A) :
    QuasiIso (ε.app (SimplicialObject.Augmented.const.obj Z)) := sorry

/-- If the alternating-face image of the simplicial augmentation is a quasi-isomorphism, then
the canonical augmented alternating-face map is a quasi-isomorphism. -/
@[stacks 019T "augmented alternating-face quasi-isomorphism"]
theorem quasiIso_ε (X : SimplicialObject.Augmented A)
    (hX : QuasiIso ((alternatingFaceMapComplex A).map X.hom)) :
    QuasiIso (ε.app X) := sorry

/-- A functorial family of augmented simplicial objects whose simplicial augmentations become
quasi-isomorphisms under alternating faces has a pointwise quasi-isomorphic canonical
augmentation natural transformation. -/
@[stacks 019T "functorial augmented alternating-face quasi-isomorphism"]
theorem quasiIso_ε_functorCategory
    {C : Type x} [Category.{y} C] (X : C ⥤ SimplicialObject.Augmented A)
    (hX : ∀ c, QuasiIso ((alternatingFaceMapComplex A).map (X.obj c).hom)) :
    (HomologicalComplex.quasiIso A (ComplexShape.down ℕ)).functorCategory C
      (Functor.whiskerLeft X ε) := sorry

/-- A simplicial homotopy-equivalence augmentation induces a quasi-isomorphism from its
alternating-face complex to its degree-zero target. -/
@[stacks 019T "homotopy-equivalence augmentation quasi-isomorphism"]
theorem quasiIso_ε_of_homotopyEquivalence (X : SimplicialObject.Augmented A)
    (hX : SimplicialObject.IsHomotopyEquivalence X.hom) :
    QuasiIso (ε.app X) := sorry

/-- A functorial family of simplicial homotopy-equivalence augmentations has a pointwise
quasi-isomorphic canonical alternating-face augmentation. -/
@[stacks 019T "functorial homotopy-equivalence augmentation quasi-isomorphism"]
theorem quasiIso_ε_functorCategory_of_homotopyEquivalence
    {C : Type x} [Category.{y} C] (X : C ⥤ SimplicialObject.Augmented A)
    (hX : ∀ c, SimplicialObject.IsHomotopyEquivalence (X.obj c).hom) :
    (HomologicalComplex.quasiIso A (ComplexShape.down ℕ)).functorCategory C
      (Functor.whiskerLeft X ε) := sorry

/-- If an additive homology-preserving functor reflecting isomorphisms detects the augmentation
as an underlying simplicial-set homotopy equivalence, then the alternating-face augmentation is
a quasi-isomorphism. -/
@[stacks 08P2 "functorially detected augmented quasi-isomorphism"]
theorem quasiIso_ε_of_inverseImage
    (F : A ⥤ AddCommGrpCat.{w}) [F.Additive] [F.PreservesHomology]
    [F.ReflectsIsomorphisms] (X : SimplicialObject.Augmented A)
    (hX : SimplicialObject.AddCommGrp.underlying.homotopyEquivalences.inverseImage
      ((Functor.whiskeringRight SimplexCategoryᵒᵖ A AddCommGrpCat.{w}).obj F) X.hom) :
    QuasiIso (ε.app X) := sorry

/-- A functorial family of augmentations detected as underlying simplicial-set homotopy
equivalences by an additive homology-preserving conservative functor has a pointwise
quasi-isomorphic canonical alternating-face augmentation. -/
@[stacks 08P2 "functorially detected family of augmented quasi-isomorphisms"]
theorem quasiIso_ε_functorCategory_of_inverseImage
    (F : A ⥤ AddCommGrpCat.{w}) [F.Additive] [F.PreservesHomology]
    [F.ReflectsIsomorphisms] {C : Type x} [Category.{y} C]
    (X : C ⥤ SimplicialObject.Augmented A)
    (hX : ∀ c, SimplicialObject.AddCommGrp.underlying.homotopyEquivalences.inverseImage
      ((Functor.whiskeringRight SimplexCategoryᵒᵖ A AddCommGrpCat.{w}).obj F)
        (X.obj c).hom) :
    (HomologicalComplex.quasiIso A (ComplexShape.down ℕ)).functorCategory C
      (Functor.whiskerLeft X ε) := sorry

end QuasiIso

end AlgebraicTopology.AlternatingFaceMapComplex

namespace CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy

variable {A : Type u} [Category.{v} A] [Preadditive A] [Limits.HasZeroObject A]
  [CategoryWithHomology A]

/-- An extra degeneracy makes the canonical alternating-face augmentation a
quasi-isomorphism. -/
@[stacks 08ND "extra degeneracy alternating-face quasi-isomorphism"]
theorem quasiIso_ε {X : SimplicialObject.Augmented A} (ed : ExtraDegeneracy X) :
    QuasiIso (AlternatingFaceMapComplex.ε.app X) := sorry

end CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy

namespace CategoryTheory.SimplicialObject.Augmented.LastExtraDegeneracy

variable {A : Type u} [Category.{v} A] [Preadditive A] [Limits.HasZeroObject A]
  [CategoryWithHomology A]

/-- A last extra degeneracy gives the alternating-face quasi-isomorphism through its canonical
simplicial homotopy equivalence. -/
@[stacks 08ND "last extra degeneracy alternating-face quasi-isomorphism"]
theorem quasiIso_ε {X : SimplicialObject.Augmented A} (ed : LastExtraDegeneracy X) :
    QuasiIso (AlternatingFaceMapComplex.ε.app X) := sorry

end CategoryTheory.SimplicialObject.Augmented.LastExtraDegeneracy
