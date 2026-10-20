/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.NaiveObstruction.VersalAt
import StacksCheckRecall

/-! # Versality and the residue homology of a naive obstruction morphism -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor DerivedCategory
open AlgebraicGeometry.GroupoidsOver

universe u

/- Lemma 98.23.3. An obstruction morphism detecting lifts and matching the
canonical tangent element yields versality from its residue homology criterion;
at a closed finite type point versality also implies the criterion. -/
@[stacks 07YM] #check (AlgebraicGeometry.GroupoidsOver.isVersalAt_of_homology :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {ξ : ObjectOverAffineOpen X} [LocallyOfFiniteType ξ.toS]
    {E : Minus (ModuleCat.{u} ξ.carrier)}
    (obstructionMap :
      Minus.ι.obj E ⟶ Algebra.naiveCotangentObject ξ.base ξ.carrier)
    (u0 : Spec (CommRingCat.of ξ.carrier)) [IsFiniteTypePoint u0]
    [Algebra ξ.carrier (residueFieldType u0)]
    (hπ :
      Spec.map (CommRingCat.ofHom
          (algebraMap ξ.carrier (residueFieldType u0))) =
        fromResidueField u0)
    (h_lifts : detectsLifts obstructionMap)
    (iso : tangentFunctor ξ.toObjectOverSpec.toFiber ≅
      DerivedCategory.Ext.moduleFunctor (Minus.ι.obj E) (0 : ℤ))
    (h_canonical : matchesCanonical obstructionMap iso)
    (h_hom : HomologyCriterion obstructionMap (residueFieldType u0)),
    IsVersalAt ξ.toS ξ.obj ξ.over_obj u0)

#check (AlgebraicGeometry.GroupoidsOver.homologyCriterion_of_isVersalAt :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {ξ : ObjectOverAffineOpen X} [LocallyOfFiniteType ξ.toS]
    {E : Minus (ModuleCat.{u} ξ.carrier)}
    (obstructionMap :
      Minus.ι.obj E ⟶ Algebra.naiveCotangentObject ξ.base ξ.carrier)
    (u0 : Spec (CommRingCat.of ξ.carrier)) [IsFiniteTypePoint u0]
    [Algebra ξ.carrier (residueFieldType u0)]
    (hπ :
      Spec.map (CommRingCat.ofHom
          (algebraMap ξ.carrier (residueFieldType u0))) =
        fromResidueField u0)
    (h_lifts : detectsLifts obstructionMap)
    (iso : tangentFunctor ξ.toObjectOverSpec.toFiber ≅
      DerivedCategory.Ext.moduleFunctor (Minus.ι.obj E) (0 : ℤ))
    (h_canonical : matchesCanonical obstructionMap iso)
    [IsVersalAt ξ.toS ξ.obj ξ.over_obj u0]
    (h_closed : IsClosed {u0}),
    HomologyCriterion obstructionMap (residueFieldType u0))

