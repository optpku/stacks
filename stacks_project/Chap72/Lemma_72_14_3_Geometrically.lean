module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.GeometricallyReduced :
  ∀ {k : Type u} [Field k],
    AlgebraicSpace (Spec (of k)) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.GeometricallyReduced.spec :
  ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))) [GeometricallyReduced X]
    (K : Type u) [Field K] [Algebra k K],
    IsReduced (baseChange (Spec.map (ofHom (algebraMap k K))) X))

#check (AlgebraicGeometry.AlgebraicSpace.GeometricallyReduced.iff :
  ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))),
    GeometricallyReduced X ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        IsReduced (baseChange (Spec.map (ofHom (algebraMap k K))) X))

#check (AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected :
  ∀ {k : Type u} [Field k],
    AlgebraicSpace (Spec (of k)) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected.spec :
  ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))) [GeometricallyConnected X]
    (K : Type u) [Field K] [Algebra k K],
    ConnectedSpace (Points (baseChange (Spec.map (ofHom (algebraMap k K))) X)))

#check (AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected.iff :
  ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))),
    GeometricallyConnected X ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        ConnectedSpace (Points (baseChange (Spec.map (ofHom (algebraMap k K))) X)))

#check (AlgebraicGeometry.AlgebraicSpace.GeometricallyIrreducible :
  ∀ {k : Type u} [Field k],
    AlgebraicSpace (Spec (of k)) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.GeometricallyIrreducible.spec :
  ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))) [GeometricallyIrreducible X]
    (K : Type u) [Field K] [Algebra k K],
    IrreducibleSpace (Points (baseChange (Spec.map (ofHom (algebraMap k K))) X)))

#check (AlgebraicGeometry.AlgebraicSpace.GeometricallyIrreducible.iff :
  ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))),
    GeometricallyIrreducible X ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        IrreducibleSpace (Points (baseChange (Spec.map (ofHom (algebraMap k K))) X)))

#check (AlgebraicGeometry.AlgebraicSpace.GeometricallyIntegral :
  ∀ {k : Type u} [Field k],
    AlgebraicSpace (Spec (of k)) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.GeometricallyIntegral.spec :
  ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))) [GeometricallyIntegral X]
    (K : Type u) [Field K] [Algebra k K],
    IsDecent (baseChange (Spec.map (ofHom (algebraMap k K))) X) ∧
      IsReduced (baseChange (Spec.map (ofHom (algebraMap k K))) X) ∧
      IrreducibleSpace (Points (baseChange (Spec.map (ofHom (algebraMap k K))) X)))

#check (AlgebraicGeometry.AlgebraicSpace.GeometricallyIntegral.iff :
  ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))),
    GeometricallyIntegral X ↔
      (∀ (K : Type u) [Field K] [Algebra k K],
          IsDecent (baseChange (Spec.map (ofHom (algebraMap k K))) X)) ∧
        (∀ (K : Type u) [Field K] [Algebra k K],
          IsReduced (baseChange (Spec.map (ofHom (algebraMap k K))) X)) ∧
        ∀ (K : Type u) [Field K] [Algebra k K],
          IrreducibleSpace (Points (baseChange (Spec.map (ofHom (algebraMap k K))) X)))

#check (AlgebraicGeometry.AlgebraicSpace.instGeometricallyReduced_ofOver_id :
  ∀ {k : Type u} [Field k],
    GeometricallyReduced (ofOver (Over.mk (𝟙 (Spec (of k))))))

#check (AlgebraicGeometry.AlgebraicSpace.instGeometricallyConnected_ofOver_id :
  ∀ {k : Type u} [Field k],
    GeometricallyConnected (ofOver (Over.mk (𝟙 (Spec (of k))))))

#check (AlgebraicGeometry.AlgebraicSpace.instGeometricallyIrreducible_ofOver_id :
  ∀ {k : Type u} [Field k],
    GeometricallyIrreducible (ofOver (Over.mk (𝟙 (Spec (of k))))))

#check (AlgebraicGeometry.AlgebraicSpace.instGeometricallyIntegral_ofOver_id :
  ∀ {k : Type u} [Field k],
    GeometricallyIntegral (ofOver (Over.mk (𝟙 (Spec (of k))))))

#check (AlgebraicGeometry.AlgebraicSpace.instGeometricallyReduced_of_geometricallyIntegral :
  ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))} [GeometricallyIntegral X],
    GeometricallyReduced X)

#check (AlgebraicGeometry.AlgebraicSpace.instGeometricallyIrreducible_of_geometricallyIntegral :
  ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))} [GeometricallyIntegral X],
    GeometricallyIrreducible X)

#check (AlgebraicGeometry.AlgebraicSpace.instGeometricallyConnected_of_geometricallyIrreducible :
  ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))} [GeometricallyIrreducible X],
    GeometricallyConnected X)

end AlgebraicGeometry.AlgebraicSpace
