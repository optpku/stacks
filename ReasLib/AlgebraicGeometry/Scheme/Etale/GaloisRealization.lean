/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.FiniteGaloisEquivalence
public import ReasLib.CategoryTheory.Action.Discrete.Orbits
public import ReasLib.AlgebraicGeometry.Scheme.FieldValuedPoint.Coproduct

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.DiscreteContAction.OrbitDecomposition
open scoped FintypeCatDiscrete

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.Etale.GaloisRealization

variable (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
  [IsSepClosure K Ksep]

/-- Realize one finite Galois orbit by the finite étale classification. -/
def orbitScheme (S : DiscreteContAction TopCat.{u} Gal(Ksep/K)) (ω : OrbitIndex S) :
    Scheme.FiniteEtale (Spec (.of K)) :=
  (finiteEtaleGaloisEquivalence K Ksep).inverse.obj (finiteOrbit S ω)

/-- The disjoint union of the finite étale schemes realizing the actual orbits. -/
def object (S : DiscreteContAction TopCat.{u} Gal(Ksep/K)) :
    Scheme.Etale (Spec (.of K)) :=
  MorphismProperty.Over.mk _ (Sigma.desc (fun ω ↦ (orbitScheme K Ksep S ω).hom))
    (IsZariskiLocalAtSource.sigmaDesc (P := @Etale)
      (fun ω ↦ (orbitScheme K Ksep S ω).prop.2))

/-- Inclusion of one realized orbit into the disjoint union. -/
def inclusion (S : DiscreteContAction TopCat.{u} Gal(Ksep/K)) (ω : OrbitIndex S) :
    (Scheme.FiniteEtale.toEtale (Spec (.of K))).obj (orbitScheme K Ksep S ω) ⟶
      object K Ksep S :=
  MorphismProperty.Over.homMk
    (Sigma.ι (fun ω ↦ (orbitScheme K Ksep S ω).left) ω) sorry

/-- An equivariant map is realized orbit by orbit and descended through the scheme coproduct. -/
def map {S T : DiscreteContAction TopCat.{u} Gal(Ksep/K)} (f : S ⟶ T) :
    object K Ksep S ⟶ object K Ksep T :=
  MorphismProperty.Over.homMk
    (Sigma.desc (fun ω ↦
      ((finiteEtaleGaloisEquivalence K Ksep).inverse.map (orbitMap f ω)).left ≫
        (inclusion K Ksep T (orbitIndexMap f ω)).left)) sorry

/-- Realization of a discrete continuous Galois set as an étale scheme over the field. -/
def functor :
    DiscreteContAction TopCat.{u} Gal(Ksep/K) ⥤ Scheme.Etale (Spec (.of K)) where
  obj := object K Ksep
  map := map K Ksep
  map_id := sorry
  map_comp := sorry

/-- A point of the realized scheme is read in its actual orbit summand, then evaluated
by the finite classification counit. -/
def counitForward (S : DiscreteContAction TopCat.{u} Gal(Ksep/K))
    (x : ((galoisFiber K Ksep).obj (object K Ksep S)).obj.obj.V) : Carrier S :=
  let z := (Scheme.FieldValuedPoint.sigmaFibreEquiv
    (fun ω ↦ (orbitScheme K Ksep S ω).left)
    (fun ω ↦ (orbitScheme K Ksep S ω).hom)
    (Spec.map (CommRingCat.ofHom (algebraMap K Ksep)))).symm x
  (((finiteEtaleGaloisEquivalence K Ksep).counitIso.hom.app
    (finiteOrbit S z.1)).hom.hom.hom z.2).val

/-- A Galois-set element determines its own orbit and the corresponding point of the
finite realization, followed by the actual coproduct inclusion. -/
def counitInverse (S : DiscreteContAction TopCat.{u} Gal(Ksep/K)) (x : Carrier S) :
    ((galoisFiber K Ksep).obj (object K Ksep S)).obj.obj.V :=
  let z := orbitDecomposition S x
  Scheme.FieldValuedPoint.sigmaFibreEquiv
    (fun ω ↦ (orbitScheme K Ksep S ω).left)
    (fun ω ↦ (orbitScheme K Ksep S ω).hom)
    (Spec.map (CommRingCat.ofHom (algebraMap K Ksep)))
    ⟨z.1, ((finiteEtaleGaloisEquivalence K Ksep).counitIso.inv.app
      (finiteOrbit S z.1)).hom.hom.hom z.2⟩

/-- The realized scheme has exactly the original discrete continuous Galois set of points. -/
def counitIso : functor K Ksep ⋙ galoisFiber K Ksep ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun S ↦ ObjectProperty.isoMk _ <| ObjectProperty.isoMk _ <|
      Action.mkIso
        { hom := @TopCat.ofHom _ _ ⊥ S.obj.obj.V.str
            (@ContinuousMap.mk _ _ ⊥ S.obj.obj.V.str (counitForward K Ksep S) sorry)
          inv := @TopCat.ofHom _ _ S.obj.obj.V.str ⊥
            (@ContinuousMap.mk _ _ S.obj.obj.V.str ⊥ (counitInverse K Ksep S) sorry)
          hom_inv_id := sorry
          inv_hom_id := sorry }
        (fun _ ↦ sorry))
    (fun _ ↦ sorry)

end AlgebraicGeometry.Scheme.Etale.GaloisRealization

end
