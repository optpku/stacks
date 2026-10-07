module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import stacks_project.Chap59.«59_56_0_1»
public import stacks_project.Chap64.Definition_64_19_1_FrobeniusStalk
public import stacks_project.Chap64.Remark_64_18_5
public import stacks_project.Chap64.Definition_64_18_6_Stalk

/-!
# Q_ℓ-stalks and geometric Frobenius at closed points

Geometric stalks of a `ℤ_[ℓ]`-sheaf, extended to `ℚ_[ℓ]`, together with the
Galois action of the inverse of residue-field arithmetic Frobenius on the
canonical geometric point over a closed point from Definition 64.19.1.
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

variable {X : Scheme.{u}} [IsNoetherian X] {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/-- Unfolding of `qellStalk` as extension of scalars of the `ℤ_[ℓ]`-stalk. -/
theorem qellStalk_def (F : ZEllSheaf X ℓ) (x : GeometricPoint X) :
    F.qellStalk x =
      (ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj
        (ModuleCat.of ℤ_[ℓ] (F.stalk x)) := sorry

/-- Constructible geometric stalks become finite-dimensional after extending
scalars from `ℤ_[ℓ]` to `ℚ_[ℓ]`. -/
theorem finiteDimensional_qellStalk
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
    (F : ZEllSheaf X ℓ) (hF : F.IsConstructible) (x : GeometricPoint X) :
    FiniteDimensional ℚ_[ℓ] (F.qellStalk x) := sorry

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf

namespace AlgebraicGeometry.Scheme.Etale.ZEllSheaf

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
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
      ⟨geometricPointFiberMap (geometricPointOverClosedPoint X x).hom
        (geometricPointGaloisIsoClosed X x σ)⟩).app (F.stage n)

/-- Stagewise Galois action on a component stalk is the sheaf-fiber map of the
geometric-point automorphism. -/
theorem componentStalkGaloisHom_spec (F : ZEllSheaf X.left ℓ)
    (x : closedPoints X.left)
    (σ : Gal(AlgebraicClosure (X.left.residueField x.1)/X.left.residueField x.1))
    (n : ℕ) :
    F.componentStalkGaloisHom x σ n =
      (Hom.sheafFiber
          ⟨geometricPointFiberMap (geometricPointOverClosedPoint X x).hom
            (geometricPointGaloisIsoClosed X x σ)⟩).app (F.stage n) := sorry

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
        (F.geometricFrobeniusStalkCone x) := sorry

/-- Geometric Frobenius on a geometric `ℤ_[ℓ]`-stalk, as a `ℤ_[ℓ]`-linear
endomorphism. -/
def geometricFrobeniusStalkZEll (F : ZEllSheaf X.left ℓ)
    (x : closedPoints X.left) :
    Module.End ℤ_[ℓ] (F.stalk (geometricPointOverClosedPoint X x)) where
  toFun := F.geometricFrobeniusStalkZEllHom x
  map_add' := sorry
  map_smul' := sorry

/-- The `ℤ_[ℓ]`-linear geometric Frobenius is the inverse-limit of the stagewise
Galois action. -/
theorem geometricFrobeniusStalkZEll_apply (F : ZEllSheaf X.left ℓ)
    (x : closedPoints X.left) (m : F.stalk (geometricPointOverClosedPoint X x)) :
    F.geometricFrobeniusStalkZEll x m = F.geometricFrobeniusStalkZEllHom x m :=
  sorry

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
          (ModuleCat.ofHom (F.geometricFrobeniusStalkZEll x))) := sorry

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf
