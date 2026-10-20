/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import ReasLib.AlgebraicGeometry.GeneralLinear.GroupScheme
public import ReasLib.AlgebraicGeometry.Scheme.OverSpec
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.RingTheory.Algebra.FreeDimensional.UnitFixing

/-!
# The unit-fixing closed subgroup of GL_d over Spec(Z)

The closed subgroup G of GL_d cut out by g(e_1) = e_1, equivalently the equations
x_11 = 1 and x_i1 = 0 for i > 1, as a group algebraic space over Spec(Z).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite CartesianMonoidalCategory MonoidalCategory
open scoped AlgebraicGeometry CategoryTheory.MonObj MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.GLFixOne

/-- The base scheme `Spec(Z)` in universe `u`. -/
abbrev specZ : Scheme.{u} :=
  Spec (CommRingCat.of (ULift.{u} ℤ))

/-- `specZ` is the spectrum of the universe-lifted integers. -/
theorem specZ_eq : specZ = Spec (CommRingCat.of (ULift.{u} ℤ)) :=
  rfl

/-- The terminal algebraic space over `specZ`. -/
abbrev base : AlgebraicSpace specZ :=
  AlgebraicSpace.ofOver (Over.mk (𝟙 specZ))

/-- `base` is `specZ` viewed as an algebraic space over itself. -/
theorem base_eq : base = AlgebraicSpace.ofOver (Over.mk (𝟙 specZ)) :=
  rfl

/-- The ideal of matrix coordinates cutting out the first-column conditions
`x_11 = 1` and `x_i1 = 0` for `i ≠ 0`. -/
def fixOneIdeal (d : ℕ) [NeZero d] :
    Ideal (GeneralLinear.coordinateRing (ULift.{u} ℤ) (ULift.{u} (Fin d))) :=
  Ideal.span
    (Set.range fun i : Fin d ↦
      GeneralLinear.localizedCoordinate (ULift.{u} ℤ) (ULift.{u} (Fin d))
          (ULift.up i) (ULift.up 0) -
        algebraMap (ULift.{u} ℤ)
          (GeneralLinear.coordinateRing (ULift.{u} ℤ) (ULift.{u} (Fin d)))
          (if i = 0 then 1 else 0))

/-- The coordinate ring of the unit-fixing closed subscheme of `GL_d`. -/
abbrev coordinateRing (d : ℕ) [NeZero d] : Type u :=
  GeneralLinear.coordinateRing (ULift.{u} ℤ) (ULift.{u} (Fin d)) ⧸ fixOneIdeal d

/-- The structure map `Z → coordinateRing d`. -/
def algebraMapHom (d : ℕ) [NeZero d] :
    CommRingCat.of (ULift.{u} ℤ) ⟶ CommRingCat.of (coordinateRing d) :=
  CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) (coordinateRing d))

/-- The unit-fixing closed subscheme of `GL_d` over `specZ`. -/
def groupOver (d : ℕ) [NeZero d] : Over specZ :=
  Scheme.OverSpec.affine (algebraMapHom d)

/-- The underlying scheme of `groupOver d` is the spectrum of `coordinateRing d`. -/
theorem groupOver_left (d : ℕ) [NeZero d] :
    (groupOver d).left = Spec (CommRingCat.of (coordinateRing d)) :=
  rfl

/-- The closed immersion of coordinate rings from `GL_d` onto the unit-fixing locus. -/
def inclusionRingHom (d : ℕ) [NeZero d] :
    GeneralLinear.coordinateRing (ULift.{u} ℤ) (ULift.{u} (Fin d)) →+* coordinateRing d :=
  Ideal.Quotient.mk (fixOneIdeal d)

/-- The closed immersion of the unit-fixing locus into `GL_d` over `specZ`. -/
def inclusionOver (d : ℕ) [NeZero d] :
    groupOver d ⟶ GeneralLinear.schemeOver (ULift.{u} ℤ) (ULift.{u} (Fin d)) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (inclusionRingHom d))) sorry

/-- The underlying scheme morphism of `inclusionOver` is `Spec` of the quotient map. -/
theorem inclusionOver_left (d : ℕ) [NeZero d] :
    (inclusionOver d).left = Spec.map (CommRingCat.ofHom (inclusionRingHom d)) :=
  rfl

/-- Reindex an invertible matrix on `ULift (Fin d)` to one on `Fin d`. -/
def reindexFin {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    (M : Matrix.GeneralLinearGroup (ULift.{u} (Fin d)) R) :
    Matrix.GeneralLinearGroup (Fin d) R where
  val := Matrix.reindex Equiv.ulift Equiv.ulift M.val
  inv := Matrix.reindex Equiv.ulift Equiv.ulift M.inv
  val_inv := sorry
  inv_val := sorry

/-- Reindex an invertible matrix on `Fin d` to one on `ULift (Fin d)`. -/
def reindexULift {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    (M : Matrix.GeneralLinearGroup (Fin d) R) :
    Matrix.GeneralLinearGroup (ULift.{u} (Fin d)) R where
  val := Matrix.reindex Equiv.ulift.symm Equiv.ulift.symm M.val
  inv := Matrix.reindex Equiv.ulift.symm Equiv.ulift.symm M.inv
  val_inv := sorry
  inv_val := sorry

/-- Convert a `ULift (Fin d)` matrix to a linear automorphism of `Fin d → R`. -/
def toLinFin {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    (M : Matrix.GeneralLinearGroup (ULift.{u} (Fin d)) R) :
    LinearMap.GeneralLinearGroup R (Fin d → R) :=
  Matrix.GeneralLinearGroup.toLin (reindexFin M)

/-- Convert a linear automorphism of `Fin d → R` to a `ULift (Fin d)` matrix. -/
def ofLinFin {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    (g : LinearMap.GeneralLinearGroup R (Fin d → R)) :
    Matrix.GeneralLinearGroup (ULift.{u} (Fin d)) R :=
  reindexULift (Matrix.GeneralLinearGroup.toLin.symm g)

/-- Morphisms over `specZ` into `groupOver d` correspond to unit-fixing automorphisms of
`Fin d → Γ(T, ⊤)`. -/
def homEquiv (d : ℕ) [NeZero d] (T : Over specZ) :
    (T ⟶ groupOver d) ≃ glFixOne Γ(T.left, ⊤) d where
  toFun f :=
    ⟨toLinFin (GeneralLinear.HomOver.equiv (ULift.{u} (Fin d)) T (f ≫ inclusionOver d)),
      sorry⟩
  invFun g :=
    Scheme.OverSpec.homOfRingHom (algebraMapHom d)
      (Under.homMk
        (CommRingCat.ofHom
          (Ideal.Quotient.lift (fixOneIdeal d)
            (Scheme.OverSpec.ringHomOfHom
                (CommRingCat.ofHom
                  (algebraMap (ULift.{u} ℤ)
                    (GeneralLinear.coordinateRing (ULift.{u} ℤ) (ULift.{u} (Fin d)))))
                ((GeneralLinear.HomOver.equiv (ULift.{u} (Fin d)) T).symm
                  (ofLinFin g.val))).right.hom
            sorry))
        sorry)
  left_inv := sorry
  right_inv := sorry

/-- The group-valued functor of unit-fixing automorphisms on free `d`-dimensional modules. -/
def functorOfPointsGrp (d : ℕ) [NeZero d] : (Over specZ)ᵒᵖ ⥤ GrpCat.{u} where
  obj T := GrpCat.of (glFixOne Γ(T.unop.left, ⊤) d)
  map f := GrpCat.ofHom (GLFixOne.map (Scheme.Γ.map f.unop.left.op).hom)
  map_id := sorry
  map_comp := sorry

/-- `functorOfPointsGrp` is represented by `groupOver d`. -/
def representableBy (d : ℕ) [NeZero d] :
    (functorOfPointsGrp d ⋙ forget GrpCat).RepresentableBy (groupOver d) where
  homEquiv {T} := homEquiv d T
  homEquiv_comp := sorry

/-- The canonical group-object structure on `groupOver d`. -/
instance instGrpObj_groupOver (d : ℕ) [NeZero d] : GrpObj (groupOver d) :=
  GrpObj.ofRepresentableBy (groupOver d) (functorOfPointsGrp d) (representableBy d)

/-- The unit-fixing closed subgroup as an algebraic space over `specZ`. -/
def space (d : ℕ) [NeZero d] : AlgebraicSpace specZ :=
  AlgebraicSpace.ofOver (groupOver d)

/-- `space d` is `ofOver` of `groupOver d`. -/
theorem space_eq (d : ℕ) [NeZero d] : space d = AlgebraicSpace.ofOver (groupOver d) :=
  rfl

/-- Multiplication of `space d`-valued points, using the group law on `groupOver d`. -/
def spaceMul {d : ℕ} [NeZero d] {E : AlgebraicSpace specZ}
    (f g : E ⟶ space d) : E ⟶ space d where
  app T := ↾fun x ↦ lift (f.app T x) (g.app T x) ≫ μ[groupOver d]
  naturality := sorry

/-- The component of `spaceMul f g` multiplies the two `T`-points. -/
theorem spaceMul_app {d : ℕ} [NeZero d] {E : AlgebraicSpace specZ}
    (f g : E ⟶ space d) (T : (Over specZ)ᵒᵖ) (x : E.functorOfPoints.obj T) :
    (spaceMul f g).app T x = lift (f.app T x) (g.app T x) ≫ μ[groupOver d] :=
  rfl

/-- The structure morphism of `space d` is smooth. -/
instance instSmooth_toBase (d : ℕ) [NeZero d] :
    AlgebraicSpace.Smooth (AlgebraicSpace.SchemeRealization.toBase (space d)) :=
  sorry

end AlgebraicGeometry.GLFixOne
