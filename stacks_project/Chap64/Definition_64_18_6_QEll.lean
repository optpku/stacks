/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Rational
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.NumberTheory.Padics.RingHoms
public import stacks_project.Chap64.Definition_64_18_1_ZEllSheaf
public import stacks_project.Chap64.Lemma_64_18_3_Category

/-!
# Torsion ℤ_[ℓ]-sheaves and Hom of ℚ_[ℓ]-sheaves

A `ℤ_[ℓ]`-sheaf is torsion when some power `ℓ ^ n • 𝟙` vanishes. Morphisms of
`ℚ_[ℓ]`-sheaves are morphisms of `ℤ_[ℓ]`-sheaves after extending scalars from
`ℤ_[ℓ]` to `ℚ_[ℓ]`; the quotient functor is the identity on objects and this
scalar extension on morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace ZEllSheaf

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [IsNoetherian X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/- The canonical owner exports the integral and rational sheaf API. -/
#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.nsmulHom :
    ∀ (F : ZEllSheaf X ℓ) (n : ℕ),
    Hom F F)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.nsmulHom_app :
    ∀ (F : ZEllSheaf X ℓ) (n k : ℕ),
    hom_app (nsmulHom F n) k = (ℓ ^ n) • 𝟙 (F.stage k))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.IsTorsion :
    ∀ (F : ZEllSheaf X ℓ),
    Prop)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.isTorsion_iff :
    ∀ (F : ZEllSheaf X ℓ),
    F.IsTorsion ↔ ∃ n : ℕ, ∀ k : ℕ, (ℓ ^ n) • 𝟙 (F.stage k) = 0)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.torsion :
    ObjectProperty (ZEllSheaf X ℓ))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.torsion_iff :
    ∀ (F : ZEllSheaf X ℓ),
    torsion F ↔ F.IsTorsion)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.homSMul :
    ∀ {F G : ZEllSheaf X ℓ} (a : ℤ_[ℓ]) (f : Hom F G),
    Hom F G)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.homSMul_app :
    ∀ {F G : ZEllSheaf X ℓ} (a : ℤ_[ℓ]) (f : Hom F G) (n : ℕ),
    (hom (homSMul a f)).app (op n) =
      (PadicInt.toZModPow (n + 1) a).val • (hom f).app (op n))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.instModuleHom :
    ∀ (F G : ZEllSheaf X ℓ),
    Module ℤ_[ℓ] (Hom F G))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.instLinear :
    Linear ℤ_[ℓ] (ZEllSheaf X ℓ))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.instIsSerreClass_torsion :
    ∀ [Abelian (ZEllSheaf X ℓ)],
    (torsion : ObjectProperty (ZEllSheaf X ℓ)).IsSerreClass)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.qellHom :
    ∀ (F G : ZEllSheaf X ℓ),
    ModuleCat ℚ_[ℓ])

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.qellHom_eq :
    ∀ (F G : ZEllSheaf X ℓ),
    qellHom F G =
      (ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj
        (ModuleCat.of ℤ_[ℓ] (Hom F G)))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.tensorQEll :
    ∀ {F G : ZEllSheaf X ℓ} (f : Hom F G),
    qellHom F G)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.tensorQEll_apply :
    ∀ {F G : ZEllSheaf X ℓ} (f : Hom F G),
    tensorQEll f = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ], algebraMap ℤ_[ℓ] ℚ_[ℓ]] f)

end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
