/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Etale.ClosedPointFrobenius

/-!
# Geometric Frobenius on adic stalks

The inverse of residue-field arithmetic Frobenius acts on component stalks,
their inverse limit, and its rational scalar extension.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.SchemeOverField
open GrothendieckTopology.Point
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Etale.ZEllSheaf

variable {k : Type u} [Field k] [Fintype k]
variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
variable {X : SchemeOverField k} [Scheme.Hom.FiniteType X.hom] [IsNoetherian X.left]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/-- Stagewise Galois action of a geometric-point automorphism on a component
stalk of a `ℤ_[ℓ]`-sheaf. -/
def componentStalkGaloisHom (F : ZEllSheaf X.left ℓ) (x : closedPoints X.left)
    (σ : Gal(AlgebraicClosure (X.left.residueField x.1)/X.left.residueField x.1))
    (n : ℕ) :
    F.componentStalk (geometricPointOverClosedPoint X x) n ⟶
      F.componentStalk (geometricPointOverClosedPoint X x) n :=
  (Hom.sheafFiber
      ⟨geometricPointFiberMap (Ω := AlgebraicClosure (X.left.residueField x.1))
        (geometricPointOverClosedPoint X x).hom
        (geometricPointGaloisIsoClosed X x σ)⟩).app (F.stage n)

/-- Stagewise Galois action on a component stalk is the sheaf-fiber map of the
geometric-point automorphism. -/
theorem componentStalkGaloisHom_spec (F : ZEllSheaf X.left ℓ)
    (x : closedPoints X.left)
    (σ : Gal(AlgebraicClosure (X.left.residueField x.1)/X.left.residueField x.1))
    (n : ℕ) :
    F.componentStalkGaloisHom x σ n =
      (Hom.sheafFiber
          ⟨geometricPointFiberMap (Ω := AlgebraicClosure (X.left.residueField x.1))
            (geometricPointOverClosedPoint X x).hom
            (geometricPointGaloisIsoClosed X x σ)⟩).app (F.stage n) := rfl

/-- The cone presenting geometric Frobenius on the inverse system of component
stalks at a closed point. -/
def geometricFrobeniusStalkCone (F : ZEllSheaf X.left ℓ)
    (x : closedPoints X.left) :
    Cone (F.componentStalkSystem (geometricPointOverClosedPoint X x)) where
  pt := F.stalk (geometricPointOverClosedPoint X x)
  π :=
    { app := fun n ↦
        F.stalk_π (geometricPointOverClosedPoint X x) n.unop ≫
          F.componentStalkGaloisHom x (arithmeticFrobeniusEquivClosed X x)⁻¹ n.unop
      naturality := sorry }

/-- Geometric Frobenius on a `ℤ_[ℓ]`-stalk, as the inverse-limit of the Galois
action of `(arithmeticFrobeniusEquivClosed X x)⁻¹`. -/
def geometricFrobeniusStalkZEllHom (F : ZEllSheaf X.left ℓ)
    (x : closedPoints X.left) :
    F.stalk (geometricPointOverClosedPoint X x) ⟶
      F.stalk (geometricPointOverClosedPoint X x) :=
  limit.lift (F.componentStalkSystem (geometricPointOverClosedPoint X x))
    (F.geometricFrobeniusStalkCone x)

/-- Unfolding of the inverse-limit morphism presenting geometric Frobenius. -/
theorem geometricFrobeniusStalkZEllHom_spec (F : ZEllSheaf X.left ℓ)
    (x : closedPoints X.left) :
    F.geometricFrobeniusStalkZEllHom x =
      limit.lift (F.componentStalkSystem (geometricPointOverClosedPoint X x))
        (F.geometricFrobeniusStalkCone x) := rfl

/-- Geometric Frobenius on a geometric `ℤ_[ℓ]`-stalk, as a `ℤ_[ℓ]`-linear
endomorphism. -/
def geometricFrobeniusStalkZEll (F : ZEllSheaf X.left ℓ)
    (x : closedPoints X.left) :
    Module.End ℤ_[ℓ] (F.stalk (geometricPointOverClosedPoint X x)) where
  toFun := F.geometricFrobeniusStalkZEllHom x
  map_add' := (F.geometricFrobeniusStalkZEllHom x).hom.map_add
  map_smul' := sorry

/-- The `ℤ_[ℓ]`-linear geometric Frobenius is the inverse-limit of the stagewise
Galois action. -/
theorem geometricFrobeniusStalkZEll_apply (F : ZEllSheaf X.left ℓ)
    (x : closedPoints X.left) (m : F.stalk (geometricPointOverClosedPoint X x)) :
    F.geometricFrobeniusStalkZEll x m = F.geometricFrobeniusStalkZEllHom x m :=
  rfl

/-- Geometric Frobenius `π_x^*` on the `ℚ_[ℓ]`-stalk at a closed point, as the
scalar extension of `geometricFrobeniusStalkZEll`. -/
def geometricFrobeniusStalk (F : ZEllSheaf X.left ℓ)
    (x : closedPoints X.left) :
    Module.End ℚ_[ℓ] (F.qellStalk (geometricPointOverClosedPoint X x)) :=
  ModuleCat.Hom.hom
    ((ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
      (ModuleCat.ofHom (F.geometricFrobeniusStalkZEll x)))

/-- Unfolding of `π_x^*` as extension of scalars of the `ℤ_[ℓ]`-linear Galois
action. -/
theorem geometricFrobeniusStalk_apply (F : ZEllSheaf X.left ℓ)
    (x : closedPoints X.left) :
    F.geometricFrobeniusStalk x =
      ModuleCat.Hom.hom
        ((ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
          (ModuleCat.ofHom (F.geometricFrobeniusStalkZEll x))) := rfl

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf
