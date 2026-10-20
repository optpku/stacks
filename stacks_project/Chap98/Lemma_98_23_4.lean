module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.NaiveObstruction.OpennessOfVersality
import StacksCheckRecall

/-! # Openness of versality from a naive obstruction morphism -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor DerivedCategory
open AlgebraicGeometry.GroupoidsOver TopologicalSpace

universe u

/- Lemma 98.23.4. A naive obstruction morphism detecting lifts, matching the
canonical tangent element, and having finite cohomology makes versality at a
closed point spread to every finite type point of an open neighbourhood. -/
@[stacks 07YN] #check (AlgebraicGeometry.GroupoidsOver.exists_isVersalAt_nhd_of_closed :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {ξ : ObjectOverAffineOpen X} [LocallyOfFiniteType ξ.toS]
    {E : Minus (ModuleCat.{u} ξ.carrier)}
    (obstructionMap :
      Minus.ι.obj E ⟶ Algebra.naiveCotangentObject ξ.base ξ.carrier)
    (u0 : Spec (CommRingCat.of ξ.carrier)) [IsFiniteTypePoint u0]
    (h_lifts : detectsLifts obstructionMap)
    (iso : tangentFunctor ξ.toObjectOverSpec.toFiber ≅
      DerivedCategory.Ext.moduleFunctor (Minus.ι.obj E) (0 : ℤ))
    (h_canonical : matchesCanonical obstructionMap iso)
    (h_finite :
      ∀ i : ℤ,
        Module.Finite ξ.carrier
          ((homologyFunctor (ModuleCat.{u} ξ.carrier) i).obj (Minus.ι.obj E)))
    [IsVersalAt ξ.toS ξ.obj ξ.over_obj u0]
    (h_closed : IsClosed {u0}),
    ∃ U' : Opens (Spec (CommRingCat.of ξ.carrier)),
      u0 ∈ U' ∧
        ∀ u, u ∈ U' → IsFiniteTypePoint u →
          IsVersalAt ξ.toS ξ.obj ξ.over_obj u)

#check (AlgebraicGeometry.GroupoidsOver.exists_basicOpen_isVersalAt_of_closed :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {ξ : ObjectOverAffineOpen X} [LocallyOfFiniteType ξ.toS]
    {E : Minus (ModuleCat.{u} ξ.carrier)}
    (obstructionMap :
      Minus.ι.obj E ⟶ Algebra.naiveCotangentObject ξ.base ξ.carrier)
    (u0 : Spec (CommRingCat.of ξ.carrier)) [IsFiniteTypePoint u0]
    (h_lifts : detectsLifts obstructionMap)
    (iso : tangentFunctor ξ.toObjectOverSpec.toFiber ≅
      DerivedCategory.Ext.moduleFunctor (Minus.ι.obj E) (0 : ℤ))
    (h_canonical : matchesCanonical obstructionMap iso)
    (h_finite :
      ∀ i : ℤ,
        Module.Finite ξ.carrier
          ((homologyFunctor (ModuleCat.{u} ξ.carrier) i).obj (Minus.ι.obj E)))
    [IsVersalAt ξ.toS ξ.obj ξ.over_obj u0]
    (h_closed : IsClosed {u0}),
    ∃ f : ξ.carrier,
      u0 ∈ (Spec (CommRingCat.of ξ.carrier)).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of ξ.carrier)).inv f) ∧
        ∀ u,
          u ∈ (Spec (CommRingCat.of ξ.carrier)).basicOpen
              ((Scheme.ΓSpecIso (CommRingCat.of ξ.carrier)).inv f) →
            IsFiniteTypePoint u →
              IsVersalAt ξ.toS ξ.obj ξ.over_obj u)
