/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.FieldTheory.Galois.Profinite
public import stacks_project.Chap58.Lemma_58_2_2_GaloisFiber
public import stacks_project.Chap59.«59_56_0_1»
public import stacks_project.Chap59.Definition_59_56_1_ResidueGalois

open CategoryTheory Opposite
open AlgebraicGeometry

@[expose] public section

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Etale

/-- The residue field of the image of a geometric point of `Spec K`. -/
abbrev residueFieldOf (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K))) :
    Type u :=
  (Spec (.of K)).residueField s.toFieldValuedPoint.image

/-- The geometric point `Spec κ(s)^sep ⟶ Spec K` through which the absolute
Galois group of `κ(s)` acts on étale stalks. -/
def geometricPointHom (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K))) :
    Spec (.of s.separableClosure) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap (residueFieldOf K s) s.separableClosure)) ≫
    (Spec (.of K)).fromSpecResidueField s.toFieldValuedPoint.image

/-- A Galois automorphism of `κ(s)^sep` induces an automorphism of
`geometricPointHom` in the slice over `Spec K`. -/
def geometricPointGaloisIso (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K))) (σ : s.absoluteGaloisGroup) :
    Over.mk (geometricPointHom K s) ≅ Over.mk (geometricPointHom K s) where
  hom := Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom)) (w := sorry)
  inv := Over.homMk (Spec.map (CommRingCat.ofHom σ.symm.toRingHom)) (w := sorry)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The separable closure of `κ(s)` is separably closed. -/
instance separableClosure_isSepClosed (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K))) :
    IsSepClosed s.separableClosure :=
  IsSepClosure.sep_closed (residueFieldOf K s)

/-- The small-étale point of `Spec K` associated to the separable closure of
`κ(s)`. -/
def etalePoint (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K))) :
    ((Spec (.of K)).smallEtaleTopology).Point :=
  Scheme.pointSmallEtale (geometricPointHom K s)

/-- The discrete continuous Galois set obtained by taking the étale stalk of a
sheaf at the geometric point determined by `κ(s)^sep`. -/
def stalkGaloisSetObj (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)) :
    DiscreteContAction TopCat s.absoluteGaloisGroup :=
  ⟨⟨
    { V := TopCat.discrete.obj ((etalePoint K s).presheafFiber.obj F.1)
      ρ :=
        { toFun := fun σ ↦
            @TopCat.ofHom _ _ ⊥ ⊥
              (@ContinuousMap.mk _ _ ⊥ ⊥
                (stalkGaloisAction (geometricPointHom K s)
                  (geometricPointGaloisIso K s σ) F.1)
                sorry)
          map_one' := sorry
          map_mul' := sorry } },
    sorry⟩,
    sorry⟩

/-- Taking étale stalks `F ↦ F_s̄` as a functor from sheaves on the small étale
site of `Spec K` to discrete continuous `Gal_κ(s)`-sets. -/
def stalkGaloisSet (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K))) :
    Sheaf (Spec (.of K)).smallEtaleTopology (Type u) ⥤
      DiscreteContAction TopCat s.absoluteGaloisGroup where
  obj := stalkGaloisSetObj K s
  map {F G} f :=
    ObjectProperty.homMk <| ObjectProperty.homMk
      { hom :=
          @TopCat.ofHom _ _ ⊥ ⊥
            (@ContinuousMap.mk _ _ ⊥ ⊥
              ((etalePoint K s).presheafFiber.map f.1) sorry)
        comm := sorry }
  map_id := sorry
  map_comp := sorry

/-- The underlying discrete space of `stalkGaloisSet` is the étale stalk at
the separable geometric point associated to `s`. -/
theorem stalkGaloisSet_obj_carrier (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)) :
    ((stalkGaloisSet K s).obj F).obj.obj.V =
      TopCat.discrete.obj ((etalePoint K s).presheafFiber.obj F.1) :=
  sorry

/-- The Galois action on a stalk is the action of `59.56.0.1` by precomposition
with the automorphism of the geometric point. -/
theorem stalkGaloisSet_smul_apply (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u))
    (σ : s.absoluteGaloisGroup)
    (x : (etalePoint K s).presheafFiber.obj F.1) :
    ConcreteCategory.hom (((stalkGaloisSet K s).obj F).obj.obj.ρ σ) x =
      stalkGaloisAction (geometricPointHom K s)
        (geometricPointGaloisIso K s σ) F.1 x :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
