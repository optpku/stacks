/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Etale.ClosedPointFrobenius
public import stacks_project.Chap59.«59_56_0_1»
public import stacks_project.Chap64.Definition_64_19_1_FrobeniusStalk
public import stacks_project.Chap64.Remark_64_18_5
public import stacks_project.Chap64.Definition_64_18_6_Stalk

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Stalk.Rational
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Frobenius

/-!
# Q_ℓ-stalks and geometric Frobenius at closed points

Geometric stalks of a `ℤ_[ℓ]`-sheaf, extended to `ℚ_[ℓ]`, together with the
Galois action of the inverse of residue-field arithmetic Frobenius on the
canonical geometric point over a closed point.
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

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.qellStalk_eq :
  ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X),
    F.qellStalk x =
      (ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj
        (ModuleCat.of ℤ_[ℓ] (F.stalk x)))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.finiteDimensional_qellStalk :
  ∀ (F : ZEllSheaf X ℓ) (hF : F.IsConstructible) (x : GeometricPoint X),
    FiniteDimensional ℚ_[ℓ] (F.qellStalk x))

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf

namespace AlgebraicGeometry.Scheme.Etale.ZEllSheaf

variable {k : Type u} [Field k] [Fintype k]
variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
variable {X : SchemeOverField k} [Scheme.Hom.FiniteType X.hom] [IsNoetherian X.left]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.componentStalkGaloisHom :
  ∀ (F : ZEllSheaf X.left ℓ) (x : closedPoints X.left)
    (σ : Gal(AlgebraicClosure (X.left.residueField x.1)/X.left.residueField x.1))
    (n : ℕ),
    F.componentStalk (geometricPointOverClosedPoint X x) n ⟶
      F.componentStalk (geometricPointOverClosedPoint X x) n)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.componentStalkGaloisHom_spec :
  ∀ (F : ZEllSheaf X.left ℓ)
    (x : closedPoints X.left)
    (σ : Gal(AlgebraicClosure (X.left.residueField x.1)/X.left.residueField x.1))
    (n : ℕ),
    F.componentStalkGaloisHom x σ n =
      (Hom.sheafFiber
          ⟨geometricPointFiberMap (Ω := AlgebraicClosure (X.left.residueField x.1))
            (geometricPointOverClosedPoint X x).hom
            (geometricPointGaloisIsoClosed X x σ)⟩).app (F.stage n))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.geometricFrobeniusStalkCone :
  ∀ (F : ZEllSheaf X.left ℓ)
    (x : closedPoints X.left),
    Cone (F.componentStalkSystem (geometricPointOverClosedPoint X x)))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.geometricFrobeniusStalkZEllHom :
  ∀ (F : ZEllSheaf X.left ℓ)
    (x : closedPoints X.left),
    F.stalk (geometricPointOverClosedPoint X x) ⟶
      F.stalk (geometricPointOverClosedPoint X x))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.geometricFrobeniusStalkZEllHom_spec :
  ∀ (F : ZEllSheaf X.left ℓ)
    (x : closedPoints X.left),
    F.geometricFrobeniusStalkZEllHom x =
      limit.lift (F.componentStalkSystem (geometricPointOverClosedPoint X x))
        (F.geometricFrobeniusStalkCone x))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.geometricFrobeniusStalkZEll :
  ∀ (F : ZEllSheaf X.left ℓ)
    (x : closedPoints X.left),
    Module.End ℤ_[ℓ] (F.stalk (geometricPointOverClosedPoint X x)))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.geometricFrobeniusStalkZEll_apply :
  ∀ (F : ZEllSheaf X.left ℓ)
    (x : closedPoints X.left) (m : F.stalk (geometricPointOverClosedPoint X x)),
    F.geometricFrobeniusStalkZEll x m = F.geometricFrobeniusStalkZEllHom x m)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.geometricFrobeniusStalk :
  ∀ (F : ZEllSheaf X.left ℓ)
    (x : closedPoints X.left),
    Module.End ℚ_[ℓ] (F.qellStalk (geometricPointOverClosedPoint X x)))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.geometricFrobeniusStalk_apply :
  ∀ (F : ZEllSheaf X.left ℓ)
    (x : closedPoints X.left),
    F.geometricFrobeniusStalk x =
      ModuleCat.Hom.hom
        ((ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
          (ModuleCat.ofHom (F.geometricFrobeniusStalkZEll x))))

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf
