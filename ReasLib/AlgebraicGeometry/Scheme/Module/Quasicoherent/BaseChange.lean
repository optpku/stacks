module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Adjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flat base change for quasi-coherent modules

This module defines the base-change transformation between restricted
quasi-coherent pullback and pushforward functors and records its invertibility
for a cartesian square with flat base morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh.BaseChange

/-- The pullback comparison attached to a commutative square of schemes. -/
noncomputable def pullbackIso {X X' T T' : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ T'} {f : X ⟶ T} {g : T' ⟶ T}
    (sq : CommSq g' f' f g) :
    Scheme.QCoh.pullback g ⋙ Scheme.QCoh.pullback f' ≅
      Scheme.QCoh.pullback f ⋙ Scheme.QCoh.pullback g' :=
  (Cat.Hom.toNatIso (Scheme.QCoh.pseudofunctor.mapComp g.op.toLoc f'.op.toLoc)).symm ≪≫
    Cat.Hom.toNatIso
      (Scheme.QCoh.pseudofunctor.map₂Iso
        (eqToIso (congrArg (fun k : X' ⟶ T ↦ k.op.toLoc) sq.w.symm))) ≪≫
      Cat.Hom.toNatIso (Scheme.QCoh.pseudofunctor.mapComp f.op.toLoc g'.op.toLoc)

/-- The canonical quasi-coherent-module base-change map of a commutative square. -/
noncomputable def map {X X' T T' : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ T'} {f : X ⟶ T} {g : T' ⟶ T}
    (sq : CommSq g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f'] :
    Scheme.QCoh.pushforward f ⋙ Scheme.QCoh.pullback g ⟶
      Scheme.QCoh.pullback g' ⋙ Scheme.QCoh.pushforward f' :=
  (mateEquiv (Scheme.QCoh.pullbackPushforwardAdjunction f)
    (Scheme.QCoh.pullbackPushforwardAdjunction f') (pullbackIso sq).hom).natTrans

/-- Flat base change makes the canonical quasi-coherent-module base-change map invertible. -/
instance map_isIso {X X' T T' : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ T'} {f : X ⟶ T} {g : T' ⟶ T}
    (sq : IsPullback g' f' f g) [Flat g]
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f'] :
    IsIso (map sq.toCommSq) := sorry

end AlgebraicGeometry.Scheme.QCoh.BaseChange
