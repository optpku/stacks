module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RestrictToScheme.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.Chart
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Equality

/-! # Derived quasi-coherent restriction along represented scheme charts

Chart restrictions use the actual right-derived `Rε_*` on `D_QCoh`. The pullback comparison
is the public unit, cell-model inverse-image square and counit construction.
-/

@[expose] public section
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory CategoryTheory.Limits
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}}
variable {X' X Y' Y : AlgebraicSpace S}
variable {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

namespace EtaleBaseChangeChart

/-- The restriction `(U → X)^* K` on the represented scheme is the actual right-derived
étale-to-Zariski direct image on quasi-coherent cohomology. -/
def restrict (c : EtaleBaseChangeChart g' f' f g) (K : DerivedQCoh X) :
    Scheme.DerivedQCoh c.U.left.left :=
  (spaceToSchemeDerived c.U.left).obj ((pullback c.U.hom).obj K)

/-- The underlying restriction computes the canonical cell-model pullback and `Rε_*`. -/
theorem restrict_eq (c : EtaleBaseChangeChart g' f' f g) (K : DerivedQCoh X) :
    (c.restrict K).obj =
      (SchemeRestriction.derived c.U.left).obj
        ((ModuleDerived.pullback c.U.hom).obj K.obj) := rfl

/-- The restriction `(U' → X')^* K'` is the same actual right-derived topology change on `U'`. -/
def restrictK' (c : EtaleBaseChangeChart g' f' f g) (sq : IsPullback g' f' f g)
    (K' : DerivedQCoh X') : Scheme.DerivedQCoh c.schemeU' :=
  (spaceToSchemeDerived c.overObj).obj ((pullback (c.toX' sq)).obj K')

/-- The chart map first uses the actual `D_QCoh` restriction-pullback comparison, then applies
`Rε_*` to the canonical pullback composition maps and `L(U' → X')^* α`. -/
def restrictMapToAmbient (c : EtaleBaseChangeChart g' f' f g) (sq : IsPullback g' f' f g)
    (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K') :
    ((Scheme.DerivedQCoh.inclusion c.schemeU').obj
        ((Scheme.DerivedQCoh.pullback c.fst).obj (c.restrict K))) ⟶
      ((Scheme.DerivedQCoh.inclusion c.schemeU').obj (c.restrictK' sq K')) :=
  (Scheme.DerivedQCoh.inclusion c.schemeU').map
      ((restrictPullbackIso c.toUOver).hom.app ((pullback c.U.hom).obj K)) ≫
    (SchemeRestriction.derived c.overObj).map
      ((ModuleDerived.pullbackCompIso (ofOverMap c.toUOver) c.U.hom).hom.app K.obj) ≫
    (SchemeRestriction.derived c.overObj).map
      ((ModuleDerived.pullbackCongr (c.toX'_comp_g' sq)).inv.app K.obj) ≫
    (SchemeRestriction.derived c.overObj).map
      ((ModuleDerived.pullbackCompIso (c.toX' sq) g').inv.app K.obj ≫
        (ModuleDerived.pullback (c.toX' sq)).map α)

/-- The restricted map `L(U' → U)^* (U → X)^* K ⟶ (U' → X')^* K'` on the scheme square. -/
def restrictMap (c : EtaleBaseChangeChart g' f' f g) (sq : IsPullback g' f' f g)
    (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K') :
    (Scheme.DerivedQCoh.pullback c.fst).obj (c.restrict K) ⟶ c.restrictK' sq K' :=
  ObjectProperty.homMk (c.restrictMapToAmbient sq K K' α)

/-- `restrictMap` is the full-subcategory morphism associated to `restrictMapToAmbient`. -/
theorem restrictMap_spec (c : EtaleBaseChangeChart g' f' f g) (sq : IsPullback g' f' f g)
    (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K') :
    ((Scheme.DerivedQCoh.inclusion c.schemeU').map (c.restrictMap sq K K' α)) =
      c.restrictMapToAmbient sq K K' α :=
  rfl

/-- The canonical cohomology base-change maps on the restricted scheme square are
isomorphisms at every point and in every integer degree. -/
def schemeHolds (c : EtaleBaseChangeChart g' f' f g) (sq : IsPullback g' f' f g)
    (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K') :
    Prop :=
  ∀ (x' : c.schemeU') (i : ℤ),
    IsIso
      ((Scheme.DerivedQCoh.CohomologyBaseChangeModel.canonical
          c.fst c.snd c.mapU.left c.mapV'.left
          (IsPullback.of_hasPullback c.mapU.left c.mapV'.left)).pointMap
        (c.restrict K) (c.restrictK' sq K') (c.restrictMap sq K K' α) x' i)

/-- The scheme base-change predicate is equivalent to pointwise invertibility of the
canonical cohomology base-change maps in every integer degree. -/
theorem schemeHolds_iff (c : EtaleBaseChangeChart g' f' f g) (sq : IsPullback g' f' f g)
    (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K') :
    c.schemeHolds sq K K' α ↔
      ∀ (x' : c.schemeU') (i : ℤ),
        IsIso
          ((Scheme.DerivedQCoh.CohomologyBaseChangeModel.canonical
              c.fst c.snd c.mapU.left c.mapV'.left
              (IsPullback.of_hasPullback c.mapU.left c.mapV'.left)).pointMap
            (c.restrict K) (c.restrictK' sq K') (c.restrictMap sq K K' α) x' i) := sorry

end EtaleBaseChangeChart

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
