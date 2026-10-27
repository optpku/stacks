/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Stalk
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import stacks_project.Chap59.Lemma_59_29_7
public import stacks_project.Chap64.Definition_64_18_1_ZEllSheaf

/-!
# Geometric stalks of ℚ_[ℓ]-sheaves

The geometric stalk of a `ℤ_[ℓ]`-sheaf is the inverse limit of the component
stalks at a geometric point, with `ℤ_[ℓ]`-action by residue nsmul. The stalk of
`F' ⊗ ℚ_[ℓ]` is that module after extending scalars to `ℚ_[ℓ]`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open GrothendieckTopology.Point

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace ZEllSheaf

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [IsNoetherian X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/- The canonical owner exports the integral and rational sheaf API. -/
#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.componentStalk :
    ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (n : ℕ),
    AddCommGrpCat.{u})

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.componentStalk_eq :
    ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (n : ℕ),
    F.componentStalk x n =
      (GeometricPoint.toSmallEtalePoint x).sheafFiber.obj (F.stage n))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.componentStalkSystem :
    ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X),
    SequentialInverseSystem AddCommGrpCat.{u})

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.componentStalkSystem_eq :
    ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X),
    F.componentStalkSystem x =
      F.system ⋙ (GeometricPoint.toSmallEtalePoint x).sheafFiber)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.stalk :
    ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X),
    AddCommGrpCat.{u})

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.stalk_eq :
    ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X),
    F.stalk x = limit (F.componentStalkSystem x))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.stalk_π :
    ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (n : ℕ),
    F.stalk x ⟶ F.componentStalk x n)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.stalk_π_eq :
    ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (n : ℕ),
    F.stalk_π x n = limit.π (F.componentStalkSystem x) (op n))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.stalkSMulπ :
    ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (a : ℤ_[ℓ]),
    (Functor.const ℕᵒᵖ).obj (F.stalk x) ⟶ F.componentStalkSystem x)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.stalkSMulπ_app :
    ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (a : ℤ_[ℓ]) (n : ℕᵒᵖ),
    (F.stalkSMulπ x a).app n =
      (PadicInt.toZModPow (n.unop + 1) a).val • limit.π (F.componentStalkSystem x) n)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.stalkSMulCone :
    ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (a : ℤ_[ℓ]),
    Cone (F.componentStalkSystem x))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.stalkSMulCone_eq :
    ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (a : ℤ_[ℓ]),
    F.stalkSMulCone x a =
      { pt := F.stalk x, π := F.stalkSMulπ x a })

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.stalkSMulHom :
    ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (a : ℤ_[ℓ]),
    F.stalk x ⟶ F.stalk x)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.stalkSMulHom_eq :
    ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (a : ℤ_[ℓ]),
    F.stalkSMulHom x a =
      limit.lift (F.componentStalkSystem x) (F.stalkSMulCone x a))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.instModuleStalk :
    ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X),
    Module ℤ_[ℓ] (F.stalk x))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.qellStalk :
    ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X),
    ModuleCat.{u} ℚ_[ℓ])

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.qellStalk_eq :
    ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X),
    F.qellStalk x =
      (ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj
        (ModuleCat.of ℤ_[ℓ] (F.stalk x)))

end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
