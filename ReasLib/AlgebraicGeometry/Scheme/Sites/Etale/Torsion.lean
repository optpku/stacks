module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk
public import Mathlib.Algebra.Category.Grp.Basic

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u v

namespace AlgebraicGeometry.Scheme.Etale

/-- The geometric stalk of an abelian sheaf on the small étale site is the sheaf
fiber of the associated small-étale point. -/
noncomputable abbrev abelianGeometricStalk {T : Scheme.{u}}
    (t : GeometricPoint T) (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{max u v}) :
    AddCommGrpCat.{max u v} :=
  (GeometricPoint.toSmallEtalePoint t).sheafFiber.obj F

/-- The abelian geometric stalk equals the sheaf fiber of the canonical small-étale point. -/
theorem abelianGeometricStalk_eq {T : Scheme.{u}} (t : GeometricPoint T)
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{max u v}) :
    abelianGeometricStalk t F =
      (GeometricPoint.toSmallEtalePoint t).sheafFiber.obj F := rfl

/-- An abelian sheaf on the small étale site of `T` has geometric stalks that are
torsion of orders invertible on `S` if every element of every geometric stalk is
annihilated by some nonzero `n : ℕ` which is a unit in `Γ(S, ⊤)`. -/
def IsTorsionWithOrdersInvertibleOn {T : Scheme.{u}} (S : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{max u v}) : Prop :=
  ∀ (t : GeometricPoint T) (a : abelianGeometricStalk t F),
    ∃ n : ℕ, n ≠ 0 ∧ n • a = 0 ∧ IsUnit (n : Γ(S, ⊤))

/-- Torsion with orders invertible on a scheme is equivalent to the existence
of an invertible nonzero natural-number annihilator for each geometric stalk element. -/
theorem isTorsionWithOrdersInvertibleOn_iff {T : Scheme.{u}} (S : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{max u v}) :
    IsTorsionWithOrdersInvertibleOn S F ↔
      ∀ (t : GeometricPoint T) (a : abelianGeometricStalk t F),
        ∃ n : ℕ, n ≠ 0 ∧ n • a = 0 ∧ IsUnit (n : Γ(S, ⊤)) := Iff.rfl

end AlgebraicGeometry.Scheme.Etale

namespace AlgebraicGeometry.Scheme

/-- An abelian étale sheaf has prime-to-characteristic torsion geometric stalks if
every stalk element has a nonzero natural annihilator with nonzero image in the
geometric point's field. -/
def geometricStalk_isPrimeToCharTorsion {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  ∀ (xbar : GeometricPoint X) (a : Etale.abelianGeometricStalk.{u, u + 1} xbar F),
    ∃ n : ℕ, n ≠ 0 ∧ n • a = 0 ∧ (n : xbar.K) ≠ 0

/-- Prime-to-characteristic torsion geometric stalks are characterized by nonzero
natural annihilators whose images in the geometric points' fields are nonzero. -/
theorem geometricStalk_isPrimeToCharTorsion_iff {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    geometricStalk_isPrimeToCharTorsion F ↔
      ∀ (xbar : GeometricPoint X) (a : Etale.abelianGeometricStalk.{u, u + 1} xbar F),
        ∃ n : ℕ, n ≠ 0 ∧ n • a = 0 ∧ (n : xbar.K) ≠ 0 :=
  Iff.rfl

end AlgebraicGeometry.Scheme
