/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_34_7_QuasiFiniteLocus
public import stacks_project.Chap79.Lemma_79_12_2_Map

/-!
# Finite-part sheaves live on the locally quasi-finite locus

The identification `(X/Y)_fin = (X'/Y)_fin` is `IsIso` of the canonical
open-immersion comparison `finitePartOpenMap` along `quasiFiniteLocus f`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical comparison of finite-part sheaves along the quasi-finite
locus of `f`. -/
def finitePartQuasiFiniteLocusMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] :
    finitePartSheaf ((quasiFiniteLocus f).ι ≫ f) ⟶ finitePartSheaf f :=
  finitePartOpenMap (quasiFiniteLocus f).ι rfl

/-- Lemma 79.12.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` which is locally of finite type. Let `X'` be the maximal open
subspace of `X` over which `f` is locally quasi-finite. Then
`IsIso (finitePartQuasiFiniteLocusMap f)` identifies
`finitePartSheaf ((quasiFiniteLocus f).ι ≫ f)` with `finitePartSheaf f`. -/
@[stacks 04PG, instance]
instance instIsIso_finitePartQuasiFiniteLocusMap {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] :
    IsIso (finitePartQuasiFiniteLocusMap f) :=
  sorry

/-- Components of `finitePartQuasiFiniteLocusMap f` are surjective on
sections. -/
theorem finitePartQuasiFiniteLocusMap_surjective {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (T : (Over S)ᵒᵖ) :
    Function.Surjective
      fun (p : FinitePart.Point ((quasiFiniteLocus f).ι ≫ f) T.unop) ↦
        FinitePart.Point.map (quasiFiniteLocus f).ι rfl p :=
  sorry

/-- A finite open subspace of `X` over `Y` lands in the quasi-finite locus of
`f` on points. -/
theorem isFinite_openSubspace_le_quasiFiniteLocus {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (U : OpenSubspace X) [IsFinite (U.ι ≫ f)] :
    Set.range (Points.map U.ι) ⊆
      Set.range (Points.map (quasiFiniteLocus f).ι) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
