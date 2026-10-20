module

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

/-- The geometric stalk of a stage at a geometric point, as an abelian group. -/
def componentStalk (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (n : ℕ) :
    AddCommGrpCat.{u} :=
  (GeometricPoint.toSmallEtalePoint x).sheafFiber.obj (F.stage n)

/-- Stage stalks are the fibre functor of the geometric point applied to the stage. -/
theorem componentStalk_eq (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (n : ℕ) :
    F.componentStalk x n =
      (GeometricPoint.toSmallEtalePoint x).sheafFiber.obj (F.stage n) := sorry

/-- The inverse system of geometric component stalks at a geometric point. -/
def componentStalkSystem (F : ZEllSheaf X ℓ) (x : GeometricPoint X) :
    SequentialInverseSystem AddCommGrpCat.{u} :=
  F.system ⋙ (GeometricPoint.toSmallEtalePoint x).sheafFiber

/-- The component-stalk system is the fibre functor applied to the inverse system. -/
theorem componentStalkSystem_eq (F : ZEllSheaf X ℓ) (x : GeometricPoint X) :
    F.componentStalkSystem x =
      F.system ⋙ (GeometricPoint.toSmallEtalePoint x).sheafFiber := sorry

/-- The geometric stalk of a `ℤ_[ℓ]`-sheaf, as the inverse limit of its component stalks. -/
def stalk (F : ZEllSheaf X ℓ) (x : GeometricPoint X) : AddCommGrpCat.{u} :=
  limit (F.componentStalkSystem x)

/-- Unfolding of the geometric `ℤ_[ℓ]`-stalk as an inverse limit. -/
theorem stalk_eq (F : ZEllSheaf X ℓ) (x : GeometricPoint X) :
    F.stalk x = limit (F.componentStalkSystem x) := sorry

/-- The cone projection from the geometric stalk onto a component stalk. -/
def stalk_π (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (n : ℕ) :
    F.stalk x ⟶ F.componentStalk x n :=
  limit.π (F.componentStalkSystem x) (op n)

/-- The stalk projection is the inverse-limit projection of `componentStalkSystem`. -/
theorem stalk_π_eq (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (n : ℕ) :
    F.stalk_π x n = limit.π (F.componentStalkSystem x) (op n) := sorry

/-- The components of scalar multiplication by a `ℤ_[ℓ]`-integer on a geometric stalk. -/
def stalkSMulπ (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (a : ℤ_[ℓ]) :
    (Functor.const ℕᵒᵖ).obj (F.stalk x) ⟶ F.componentStalkSystem x where
  app n := (PadicInt.toZModPow (n.unop + 1) a).val • limit.π (F.componentStalkSystem x) n
  naturality := sorry

/-- Components of padic scalar multiplication on a stalk are residue nsmul of the projections. -/
theorem stalkSMulπ_app (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (a : ℤ_[ℓ]) (n : ℕᵒᵖ) :
    (F.stalkSMulπ x a).app n =
      (PadicInt.toZModPow (n.unop + 1) a).val • limit.π (F.componentStalkSystem x) n := sorry

/-- The cone presenting scalar multiplication by a `ℤ_[ℓ]`-integer on a geometric stalk. -/
def stalkSMulCone (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (a : ℤ_[ℓ]) :
    Cone (F.componentStalkSystem x) where
  pt := F.stalk x
  π := F.stalkSMulπ x a

/-- The padic scalar-multiplication cone has apex the stalk and legs `stalkSMulπ`. -/
theorem stalkSMulCone_eq (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (a : ℤ_[ℓ]) :
    F.stalkSMulCone x a =
      { pt := F.stalk x, π := F.stalkSMulπ x a } := sorry

/-- The endomorphism of a geometric stalk given by scalar multiplication by a
`ℤ_[ℓ]`-integer. -/
def stalkSMulHom (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (a : ℤ_[ℓ]) :
    F.stalk x ⟶ F.stalk x :=
  limit.lift (F.componentStalkSystem x) (F.stalkSMulCone x a)

/-- Unfolding of padic scalar multiplication on a geometric stalk as a limit lift. -/
theorem stalkSMulHom_eq (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (a : ℤ_[ℓ]) :
    F.stalkSMulHom x a =
      limit.lift (F.componentStalkSystem x) (F.stalkSMulCone x a) := sorry

/-- The `ℤ_[ℓ]`-module structure on a geometric stalk, via compatible residue actions. -/
instance instModuleStalk (F : ZEllSheaf X ℓ) (x : GeometricPoint X) :
    Module ℤ_[ℓ] (F.stalk x) where
  smul a y := F.stalkSMulHom x a y
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- The geometric stalk of `F' ⊗ ℚ_[ℓ]` at a geometric point, as
`F'_x̄ ⊗[ℤ_[ℓ]] ℚ_[ℓ]`. -/
def qellStalk (F : ZEllSheaf X ℓ) (x : GeometricPoint X) : ModuleCat.{u} ℚ_[ℓ] :=
  (ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj
    (ModuleCat.of ℤ_[ℓ] (F.stalk x))

/-- Unfolding of `qellStalk` as extension of scalars of the geometric inverse-limit
`ℤ_[ℓ]`-module. -/
theorem qellStalk_eq (F : ZEllSheaf X ℓ) (x : GeometricPoint X) :
    F.qellStalk x =
      (ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj
        (ModuleCat.of ℤ_[ℓ] (F.stalk x)) := sorry

end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
