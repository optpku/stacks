module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.QuasiFiniteLocus
import StacksCheckRecall

/-!
# Finite-part sheaves live on the locally quasi-finite locus

The identification `(X/Y)_fin = (X'/Y)_fin` is `IsIso` of the canonical
open-immersion comparison `finitePartOpenMap` along `quasiFiniteLocus f`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 79.12.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` which is locally of finite type. Let `X'` be the maximal open
subspace of `X` over which `f` is locally quasi-finite. Then
`IsIso (finitePartQuasiFiniteLocusMap f)` identifies
`finitePartSheaf ((quasiFiniteLocus f).ι ≫ f)` with `finitePartSheaf f`. -/
@[stacks 04PG] #check
  (AlgebraicGeometry.AlgebraicSpace.instIsIso_finitePartQuasiFiniteLocusMap :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f],
      IsIso (finitePartQuasiFiniteLocusMap f))
