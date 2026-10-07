module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.Fiber
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IsSepClosed

@[expose] public section
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme
variable (K : Type u) [Field K]

/-- The separably closed point of the spectrum of a field obtained from its
actual separable closure and structure algebra map. -/
def separableClosurePoint : Spec (.of (SeparableClosure K)) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure K)))

/-- A field Galois automorphism gives an automorphism over Spec K of its
specified separable-closure point. -/
theorem separableClosurePointAut_fac (σ : Gal(SeparableClosure K/K)) :
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ separableClosurePoint K =
      separableClosurePoint K := sorry

/-- A field Galois automorphism gives an automorphism over Spec K of its
specified separable-closure point; its underlying map is Spec sigma. -/
def separableClosurePointAut (σ : Gal(SeparableClosure K/K)) :
    Over.mk (separableClosurePoint K) ≅ Over.mk (separableClosurePoint K) where
  hom := Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom)) (separableClosurePointAut_fac K σ)
  inv := Over.homMk (Spec.map (CommRingCat.ofHom σ.symm.toRingHom)) (separableClosurePointAut_fac K σ.symm)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Forget finiteness of a finite étale scheme, retaining its actual étale map. -/
def finiteEtaleAsEtale {X : Scheme.{u}} (V : FiniteEtale X) : X.Etale :=
  { left := V.left, right := V.right, hom := V.hom, prop := V.prop.2 }

/-- The Galois action on the finite étale fiber uses the existing geometric
point action, namely precomposition by Spec sigma on every lift. -/
def fieldGaloisAut (σ : Gal(SeparableClosure K/K)) :
    fundamentalGroup (separableClosurePoint K) :=
  NatIso.ofComponents (fun V ↦
    { hom := FintypeCat.homMk
        ((Etale.geometricPointFiberMap (separableClosurePoint K)
          (separableClosurePointAut K σ)).app (finiteEtaleAsEtale V))
      inv := FintypeCat.homMk
        ((Etale.geometricPointFiberMap (separableClosurePoint K)
          (separableClosurePointAut K σ).symm).app (finiteEtaleAsEtale V))
      hom_inv_id := sorry
      inv_hom_id := sorry }) (fun _ ↦ sorry)

/-- The canonical continuous Galois-to-fundamental-group map acts on the
actual finite étale fibers of the specified separable-closure point. -/
def fieldGaloisMap : ContinuousMonoidHom Gal(SeparableClosure K/K)
    (fundamentalGroup (separableClosurePoint K)) where
  toFun := fieldGaloisAut K
  map_one' := sorry
  map_mul' := sorry
  continuous_toFun := sorry

/-- The forward action has exactly the Spec-sigma precomposition orientation. -/
theorem fieldGaloisMap_apply_left (σ : Gal(SeparableClosure K/K))
    (V : FiniteEtale (Spec (.of K)))
    (x : (finiteEtaleFiberType (separableClosurePoint K)).obj V) :
    (((fieldGaloisMap K σ).hom.app V) x).left =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.left := rfl

/-- The finite étale field correspondence makes this specified action map bijective. -/
theorem fieldGaloisMap_bijective : Function.Bijective (fieldGaloisMap K) := sorry

/-- The field Galois identification is the inverse of the specified fiber-action
map, rather than an externally supplied identification of abstract groups. -/
def fieldGaloisEquiv : Gal(SeparableClosure K/K) ≃* fundamentalGroup (separableClosurePoint K) :=
  MulEquiv.ofBijective (fieldGaloisMap K).toMonoidHom (fieldGaloisMap_bijective K)

/-- The canonical field identification respects the Krull and fiber-automorphism topologies. -/
theorem fieldGaloisMap_isHomeomorph : IsHomeomorph (fieldGaloisMap K) := sorry

end AlgebraicGeometry.Scheme
