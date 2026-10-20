/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Bicategorical
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Property
public import ReasLib.CategoryTheory.Fibered.Criteria

/-!
# Strongly cartesian morphisms under equivalence over a base

This module provides the general rebasing lemma for strongly cartesian morphisms and the two
canonical equivalence-transport interfaces: `BasedFunctor.IsEquivalence` for heterogeneous
universes and `BasedCategory.Equivalence` inside one fixed bicategory.
-/

@[expose] public section

universe v u vX uX vY uY vB uB vE uE vS uS

namespace CategoryTheory

open Functor
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace Functor.IsStronglyCartesian

/-- Strong cartesianness of a fixed total-category morphism is independent of the chosen displayed
base arrow, provided that the same morphism is a lift of the new base arrow. -/
protected theorem rebase
    {𝒮 : Type uB} {𝒳 : Type uE} [Category.{vB} 𝒮] [Category.{vE} 𝒳]
    {p : 𝒳 ⥤ 𝒮} {R S R' S' : 𝒮} {x y : 𝒳}
    {f : R ⟶ S} {f' : R' ⟶ S'} {φ : x ⟶ y}
    (hφ : p.IsStronglyCartesian f φ) (hφ' : p.IsHomLift f' φ) :
    p.IsStronglyCartesian f' φ := sorry
/- Proof strategy: use the two hom-lift structures to identify both pairs of external endpoints
with `p.obj x` and `p.obj y`, then identify `f` and `f'` with `p.map φ`; after eliminating those
equalities, the conclusion is exactly `hφ`. -/

end Functor.IsStronglyCartesian

namespace BasedFunctor.IsEquivalence

variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

/-- An equivalence over the base category sends strongly cartesian morphisms to strongly
cartesian morphisms. -/
theorem isStronglyCartesian_map
    (F : X ⥤ᵇ Y) [F.IsEquivalence]
    {x y : X.obj} (φ : x ⟶ y)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ) :
    Y.p.IsStronglyCartesian (Y.p.map (F.map φ)) (F.map φ) := sorry
/- Proof strategy: choose `e := F.asQuasiInverse`. Pull an arbitrary lifting problem for `F.map φ`
back along `e.inverse` using `e.inverse.isHomLift_iff`, and compose with the appropriate component
of `e.unitIso` to obtain a lifting problem for `φ`. Apply
`IsStronglyCartesian.universal_property` to `hφ`, map the unique factorization forward with `F`,
and correct its source by the inverse component of `e.counitIso`. Naturality and the inverse laws
of `e.unitIso` and `e.counitIso` prove factorization and uniqueness; their based-natural-
transformation hom-lift fields, together with `F.w` and `e.inverse.w`, discharge every base-arrow
transport. This argument uses only the heterogeneous `QuasiInverse` fields and needs no
bicategorical adjointification. -/

/-- A based equivalence over the base preserves strongly cartesian morphisms. -/
theorem preservesStronglyCartesian (F : X ⥤ᵇ Y) [F.IsEquivalence] :
    F.PreservesStronglyCartesian := sorry
/- Proof strategy: apply `BasedFunctor.IsEquivalence.isStronglyCartesian_map F` to each strongly
cartesian source morphism. -/

end BasedFunctor.IsEquivalence

namespace BasedCategory.Equivalence

variable {X Y : BasedCategory.{vS, uS} C}

/-- The forward `1`-morphism of an equivalence in `BasedCategory C` sends strongly cartesian
morphisms to strongly cartesian morphisms. This is the canonical same-universe form of transport;
the equivalence object retains access to all bicategorical composition and coherence API. -/
theorem isStronglyCartesian_map
    (e : X ≌ Y) {x y : X.obj} (φ : x ⟶ y)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ) :
    Y.p.IsStronglyCartesian (Y.p.map (e.hom.map φ)) (e.hom.map φ) := sorry
/- Proof strategy: apply the heterogeneous compatibility theorem
`BasedFunctor.IsEquivalence.isStronglyCartesian_map` to `e.hom` after extracting its based
quasi-inverse from `e.inv`, `e.unit`, and `e.counit`. -/

end BasedCategory.Equivalence

end CategoryTheory
