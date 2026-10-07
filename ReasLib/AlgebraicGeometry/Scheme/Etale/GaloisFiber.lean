module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import ReasLib.CategoryTheory.Action.Continuous
public import Mathlib.FieldTheory.Galois.Profinite

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Etale

/-- Precomposition by a Galois automorphism on the `Spec Ksep`-points of an étale scheme
over `Spec K`. -/
noncomputable def galoisPointAction
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (X : Scheme.Etale (Spec (.of K))) (σ : Gal(Ksep/K))
    (x : (@Scheme.pointSmallEtale (Spec (.of K)) Ksep inferInstance
      (IsSepClosure.sep_closed K)
      (Spec.map (CommRingCat.ofHom (algebraMap K Ksep)))).fiber.obj X) :
    (@Scheme.pointSmallEtale (Spec (.of K)) Ksep inferInstance
      (IsSepClosure.sep_closed K)
      (Spec.map (CommRingCat.ofHom (algebraMap K Ksep)))).fiber.obj X :=
  Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.left) (w := sorry)

/-- The geometric-fiber functor from schemes étale over `Spec K` to discrete continuous
actions of `Gal(Ksep/K)` on their `Spec Ksep`-points. -/
noncomputable def galoisFiber
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] :
    Scheme.Etale (Spec (.of K)) ⥤ DiscreteContAction TopCat Gal(Ksep/K) :=
  let s : Spec (.of Ksep) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K Ksep))
  { obj := fun X ↦
      ⟨⟨
        { V := TopCat.discrete.obj
            ((@Scheme.pointSmallEtale (Spec (.of K)) Ksep inferInstance
              (IsSepClosure.sep_closed K) s).fiber.obj X)
          ρ :=
            { toFun := fun σ ↦
                @TopCat.ofHom _ _ ⊥ ⊥
                  (@ContinuousMap.mk _ _ ⊥ ⊥ (galoisPointAction K Ksep X σ) sorry),
              map_one' := sorry
              map_mul' := sorry } },
        sorry⟩,
        sorry⟩
    map := fun f ↦
      ObjectProperty.homMk <| ObjectProperty.homMk
        { hom := @TopCat.ofHom _ _ ⊥ ⊥
            (@ContinuousMap.mk _ _ ⊥ ⊥
              ((@Scheme.pointSmallEtale (Spec (.of K)) Ksep inferInstance
                (IsSepClosure.sep_closed K) s).fiber.map f) sorry),
          comm := sorry }
    map_id := sorry
    map_comp := sorry }

/-- The underlying discrete topological space of `galoisFiber` is the canonical
`pointSmallEtale` fiber of `Spec Ksep ⟶ Spec K`. -/
theorem galoisFiber_obj_carrier
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (X : Scheme.Etale (Spec (.of K))) :
    ((galoisFiber K Ksep).obj X).obj.obj.V =
      TopCat.discrete.obj
        ((@Scheme.pointSmallEtale (Spec (.of K)) Ksep inferInstance
          (IsSepClosure.sep_closed K)
          (Spec.map (CommRingCat.ofHom (algebraMap K Ksep)))).fiber.obj X) := sorry

/-- The Galois action on a geometric point is precomposition with the scheme automorphism
induced by the corresponding automorphism of `Ksep`. -/
theorem galoisFiber_smul_apply
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (X : Scheme.Etale (Spec (.of K))) (σ : Gal(Ksep/K))
    (x : (@Scheme.pointSmallEtale (Spec (.of K)) Ksep inferInstance
      (IsSepClosure.sep_closed K)
      (Spec.map (CommRingCat.ofHom (algebraMap K Ksep)))).fiber.obj X) :
    ConcreteCategory.hom (((galoisFiber K Ksep).obj X).obj.obj.ρ σ) x =
      galoisPointAction K Ksep X σ x := sorry

/-- The map on geometric fibers induced by an étale morphism is postcomposition. -/
theorem galoisFiber_map_apply
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    {X Y : Scheme.Etale (Spec (.of K))} (f : X ⟶ Y)
    (x : (@Scheme.pointSmallEtale (Spec (.of K)) Ksep inferInstance
      (IsSepClosure.sep_closed K)
      (Spec.map (CommRingCat.ofHom (algebraMap K Ksep)))).fiber.obj X) :
    ((CategoryTheory.forget₂ (DiscreteContAction TopCat Gal(Ksep/K)) TopCat).map
      ((galoisFiber K Ksep).map f)) x =
      x ≫ (Scheme.Etale.forget (Spec (.of K))).map f := sorry

/-- The geometric-fiber functor identifies étale schemes over a field with discrete
continuous actions of the Galois group of a chosen separable closure. -/
instance galoisFiberIsEquivalence
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] :
    (galoisFiber K Ksep).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.Etale

end
