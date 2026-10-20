/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.KanExtension.Pointwise
public import ReasLib.AlgebraicTopology.SimplicialSet.Truncated.SkeletonULift
public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.ConstHom
public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Functor.Constant
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Skeletons and simplicial copowers

This file owns the canonical comparison between the skeleton of a copower by a constant
simplicial object and the copower indexed by the skeleton.  Its Hom equivalence is assembled
from the skeleton adjunctions and the constant-source tensor-hom equivalences.  The objectwise
comparison is packaged naturally in both the constant-object and indexing variables.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

namespace copower

namespace truncation

section SkeletonIndex

variable (n : ℕ) (U : SSet.{w}) (X : C)
variable [HasCopower U ((const C).obj X)]
variable [HasCopower ((SSet.sk n).obj U) ((const C).obj X)]

/-- Maps from the truncation of a constant copower are equivalently maps from the copower
indexed by the simplicial-set skeleton. This is the coefficient-category-free core of the
skeleton-copower comparison. -/
@[stacks 018V "truncated copower and skeleton-indexed copower Hom equivalence"]
noncomputable def skeletonHomEquiv (V : SimplicialObject C) :
    ((truncation n).obj (copower U ((const C).obj X)) ⟶ (truncation n).obj V) ≃
      (copower ((SSet.sk n).obj U) ((const C).obj X) ⟶ V) :=
  (copower.truncation.constHom.uliftEquiv n U X V).trans
    ((SSet.sk.uliftHomEquiv n U (Functor.homFromConst X V)).trans
      (copower.constHom.uliftEquiv ((SSet.sk n).obj U) X V).symm)

/-- The truncated-copower equivalence is natural under postcomposition. -/
@[stacks 018V "truncated skeleton-indexed copower target naturality"]
theorem skeletonHomEquiv.comp {V W : SimplicialObject C}
    (f : (truncation n).obj (copower U ((const C).obj X)) ⟶ (truncation n).obj V)
    (g : V ⟶ W) :
    skeletonHomEquiv n U X W (f ≫ (truncation n).map g) =
      skeletonHomEquiv n U X V f ≫ g := sorry

/-- The truncated-copower equivalence is contravariantly natural in the constant object. -/
@[stacks 018V "truncated skeleton-indexed copower source naturality"]
theorem skeletonHomEquiv.precomp {Y : C} {V : SimplicialObject C}
    [HasCopower U ((const C).obj Y)]
    [HasCopower ((SSet.sk n).obj U) ((const C).obj Y)]
    (f : X ⟶ Y)
    (g : (truncation n).obj (copower U ((const C).obj Y)) ⟶ (truncation n).obj V) :
    skeletonHomEquiv n U X V
        ((truncation n).map (copower.hom U ((const C).map f)) ≫ g) =
      copower.hom ((SSet.sk n).obj U) ((const C).map f) ≫
        skeletonHomEquiv n U Y V g := sorry

end SkeletonIndex

end truncation

namespace skeleton

section SkeletonComparison

variable (n : ℕ)
variable [SimplicialObject.Truncated.HasSkeletons C n]
variable (U : SSet.{w}) (X : C)
variable [hU : HasCopower U ((const C).obj X)]
variable [hskU : HasCopower ((SSet.sk n).obj U) ((const C).obj X)]

/-- The natural Hom equivalence expressing that skeleton commutes with a copower by a constant
simplicial object. -/
@[stacks 018V "skeleton-copower Hom equivalence"]
noncomputable def homEquiv (V : SimplicialObject C) :
    ((sk n).obj (copower U ((const C).obj X)) ⟶ V) ≃
      (copower ((SSet.sk n).obj U) ((const C).obj X) ⟶ V) :=
  ((skAdj n).homEquiv
      ((truncation n).obj (copower U ((const C).obj X))) V).trans
    ((copower.truncation.constHom.uliftEquiv n U X V).trans
      ((SSet.sk.uliftHomEquiv n U (Functor.homFromConst X V)).trans
        (copower.constHom.uliftEquiv ((SSet.sk n).obj U) X V).symm))

/-- The skeleton-copower Hom equivalence is natural under postcomposition. -/
@[stacks 018V "skeleton-copower Hom equivalence naturality"]
theorem homEquiv.comp {V W : SimplicialObject C}
    (f : (sk n).obj (copower U ((const C).obj X)) ⟶ V) (g : V ⟶ W) :
    homEquiv n U X W (f ≫ g) =
      homEquiv n U X V f ≫ g := sorry

/-- The forward comparison morphism from the skeleton of a constant copower. -/
@[stacks 018V "skeleton-copower comparison morphism"]
noncomputable def iso.hom :
    (sk n).obj (copower U ((const C).obj X)) ⟶
      copower ((SSet.sk n).obj U) ((const C).obj X) :=
  (homEquiv n U X
    (copower ((SSet.sk n).obj U) ((const C).obj X))).symm
      (𝟙 (copower ((SSet.sk n).obj U) ((const C).obj X)))

/-- The inverse comparison morphism from the copower indexed by the skeleton. -/
@[stacks 018V "inverse skeleton-copower comparison morphism"]
noncomputable def iso.inv :
    copower ((SSet.sk n).obj U) ((const C).obj X) ⟶
      (sk n).obj (copower U ((const C).obj X)) :=
  homEquiv n U X ((sk n).obj (copower U ((const C).obj X)))
    (𝟙 ((sk n).obj (copower U ((const C).obj X))))

/-- The forward and inverse skeleton-copower comparison maps compose to the identity. -/
@[stacks 018V]
theorem iso.hom_inv_id :
    iso.hom n U X ≫ iso.inv n U X =
      𝟙 ((sk n).obj (copower U ((const C).obj X))) := sorry

/-- The inverse and forward skeleton-copower comparison maps compose to the identity. -/
@[stacks 018V]
theorem iso.inv_hom_id :
    iso.inv n U X ≫ iso.hom n U X =
      𝟙 (copower ((SSet.sk n).obj U) ((const C).obj X)) := sorry

/-- Tag 018V, skeleton-copower comparison: skeleton commutes with a simplicial-set copower by a
constant simplicial object whenever the displayed copowers exist. -/
@[stacks 018V "skeleton-copower comparison"]
noncomputable def iso :
    (sk n).obj (copower U ((const C).obj X)) ≅
      copower ((SSet.sk n).obj U) ((const C).obj X) where
  hom := iso.hom n U X
  inv := iso.inv n U X
  hom_inv_id := iso.hom_inv_id n U X
  inv_hom_id := iso.inv_hom_id n U X

namespace iso

/-- The skeleton-copower comparison is characterized by the skeleton unit after truncation. -/
@[stacks 018V]
theorem unit :
    (skAdj n).unit.app ((truncation n).obj (copower U ((const C).obj X))) ≫
        (truncation n).map (iso n U X).hom =
      copower.truncation.indexHom (U := U) (W := (SSet.sk n).obj U) n ((const C).obj X)
        ((SSet.skAdj n).unit.app ((SSet.truncation n).obj U)) := sorry

/-- The skeleton-copower comparison intertwines the two canonical skeleton counits. -/
@[stacks 018V]
theorem counit :
    (iso n U X).hom ≫
        copower.indexHom (U := (SSet.sk n).obj U) (V := U) ((const C).obj X)
          ((SSet.skAdj n).counit.app U) =
      (skAdj n).counit.app (copower U ((const C).obj X)) := sorry

/-- The skeleton-copower comparison is natural in the constant object. -/
@[stacks 018V]
theorem object.naturality {Y : C}
    [HasCopower U ((const C).obj Y)]
    [HasCopower ((SSet.sk n).obj U) ((const C).obj Y)] (f : X ⟶ Y) :
    (sk n).map (copower.hom U ((const C).map f)) ≫
        (iso n U Y).hom =
      (iso n U X).hom ≫
        copower.hom ((SSet.sk n).obj U) ((const C).map f) := sorry

end iso

end SkeletonComparison

namespace object

section ObjectComparison

variable (n : ℕ) [SimplicialObject.Truncated.HasSkeletons C n]
variable (U : SSet.{w})
variable [HasConstCopowers U C]
variable [HasConstCopowers ((SSet.sk n).obj U) C]

/-- The skeleton-copower comparison is a natural isomorphism in the constant object. -/
@[stacks 018V "skeleton-copower comparison natural in the constant object"]
noncomputable def natIso :
    copower.constFunctor (C := C) U ⋙ sk n ≅
      copower.constFunctor (C := C) ((SSet.sk n).obj U) :=
  NatIso.ofComponents (fun X ↦ iso n U X)
    (fun f ↦ iso.object.naturality n U _ f)

namespace natIso

/-- Evaluating the constant-object natural comparison recovers the canonical objectwise
skeleton-copower comparison. -/
@[simp, stacks 018V "component of the constant-object skeleton-copower comparison"]
theorem app (X : C) :
    (object.natIso (C := C) n U).app X = iso n U X := sorry

/-- The forward component of the constant-object natural comparison is the objectwise
skeleton-copower comparison. -/
@[simp, stacks 018V "forward component of the constant-object skeleton-copower comparison"]
theorem hom_app (X : C) :
    (object.natIso (C := C) n U).hom.app X = (iso n U X).hom := sorry

/-- The inverse component of the constant-object natural comparison is the inverse objectwise
skeleton-copower comparison. -/
@[simp, stacks 018V "inverse component of the constant-object skeleton-copower comparison"]
theorem inv_app (X : C) :
    (object.natIso (C := C) n U).inv.app X = (iso n U X).inv := sorry

end natIso

end ObjectComparison

end object

namespace iso

section IndexNaturality

variable (n : ℕ) [SimplicialObject.Truncated.HasSkeletons C n]
variable (U : SSet.{w}) (X : C)
variable [copowerU : HasCopower U ((SimplicialObject.const C).obj X)]
variable [copowerSkU : HasCopower ((SSet.sk n).obj U) ((SimplicialObject.const C).obj X)]

/-- The skeleton-copower comparison is natural in the indexing simplicial set. -/
@[stacks 018V]
theorem index.naturality {W : SSet.{w}}
    [copowerW : HasCopower W ((SimplicialObject.const C).obj X)]
    [copowerSkW : HasCopower ((SSet.sk n).obj W) ((SimplicialObject.const C).obj X)]
    (a : U ⟶ W) :
    (sk n).map (copower.indexHom (U := U) (V := W)
      ((SimplicialObject.const C).obj X) a) ≫
        (iso n W X).hom =
      (iso n U X).hom ≫
        copower.indexHom (U := (SSet.sk n).obj U) (V := (SSet.sk n).obj W)
          ((SimplicialObject.const C).obj X) ((SSet.sk n).map a) := sorry

end IndexNaturality

end iso

namespace index

section IndexComparison

variable (n : ℕ) [SimplicialObject.Truncated.HasSkeletons C n]
variable (X : C) [((SimplicialObject.const C).obj X).HasCopowersOf]

/-- The skeleton-copower comparison is a natural isomorphism in the indexing simplicial set. -/
@[stacks 018V "skeleton-copower comparison natural in the indexing simplicial set"]
noncomputable def natIso :
    copower.indexFunctor ((SimplicialObject.const C).obj X) ⋙ SimplicialObject.sk n ≅
      SSet.sk n ⋙ copower.indexFunctor ((SimplicialObject.const C).obj X) :=
  NatIso.ofComponents (fun U ↦ iso n U X)
    (fun {_ _} a ↦ iso.index.naturality n _ X a)

namespace natIso

/-- Evaluating the index-variable natural comparison recovers the canonical objectwise
skeleton-copower comparison. -/
@[simp, stacks 018V "component of the index-variable skeleton-copower comparison"]
theorem app (U : SSet.{w}) :
    (index.natIso (C := C) n X).app U = iso n U X := sorry

/-- The forward component of the index-variable natural comparison is the objectwise
skeleton-copower comparison. -/
@[simp, stacks 018V "forward component of the index-variable skeleton-copower comparison"]
theorem hom_app (U : SSet.{w}) :
    (index.natIso (C := C) n X).hom.app U = (iso n U X).hom := sorry

/-- The inverse component of the index-variable natural comparison is the inverse objectwise
skeleton-copower comparison. -/
@[simp, stacks 018V "inverse component of the index-variable skeleton-copower comparison"]
theorem inv_app (U : SSet.{w}) :
    (index.natIso (C := C) n X).inv.app U = (iso n U X).inv := sorry

end natIso

end IndexComparison

end index

end skeleton

end copower

end CategoryTheory.SimplicialObject
