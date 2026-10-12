/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import ReasLib.AlgebraicGeometry.GeneralLinear.GroupScheme
public import stacks_project.Chap65.Lemma_65_7_1_Product
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap78.Definition_78_5_1_Group
public import stacks_project.Chap78.Example_78_7_4_General_linear_group_algebraic_space_GeneralLinear
public import stacks_project.Chap97.Lemma_97_13_1_FixOne

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
  sorry

/-- The terminal algebraic space over `specZ`. -/
abbrev base : AlgebraicSpace specZ :=
  AlgebraicSpace.ofOver (Over.mk (𝟙 specZ))

/-- `base` is `specZ` viewed as an algebraic space over itself. -/
theorem base_eq : base = AlgebraicSpace.ofOver (Over.mk (𝟙 specZ)) :=
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- The unit-fixing closed subgroup as an object of the slice over `base`. -/
def asOver (d : ℕ) [NeZero d] : Over base :=
  Over.mk (AlgebraicSpace.toBase (space d))

/-- `asOver d` is `Over.mk` of the unique morphism `space d ⟶ base`. -/
theorem asOver_eq (d : ℕ) [NeZero d] :
    asOver d = Over.mk (AlgebraicSpace.toBase (space d)) :=
  sorry

/-- Multiplication of `space d`-valued points, using the group law on `groupOver d`. -/
def spaceMul {d : ℕ} [NeZero d] {E : AlgebraicSpace specZ}
    (f g : E ⟶ space d) : E ⟶ space d where
  app T := ↾fun x ↦ lift (f.app T x) (g.app T x) ≫ μ[groupOver d]
  naturality := sorry

/-- The component of `spaceMul f g` multiplies the two `T`-points. -/
theorem spaceMul_app {d : ℕ} [NeZero d] {E : AlgebraicSpace specZ}
    (f g : E ⟶ space d) (T : (Over specZ)ᵒᵖ) (x : E.functorOfPoints.obj T) :
    (spaceMul f g).app T x = lift (f.app T x) (g.app T x) ≫ μ[groupOver d] :=
  sorry

/-- The unit section of `asOver d`. -/
def one (d : ℕ) [NeZero d] : 𝟙_ (Over base) ⟶ asOver d :=
  Over.homMk
    (AlgebraicSpace.ofOverMap (η[groupOver d]))
    sorry

/-- The underlying algebraic-space map of `one d` is `ofOverMap` of the scheme-level unit. -/
theorem one_left (d : ℕ) [NeZero d] :
    (one d).left = AlgebraicSpace.ofOverMap (η[groupOver d]) :=
  sorry

/-- The inverse morphism of `asOver d`. -/
def inv (d : ℕ) [NeZero d] : asOver d ⟶ asOver d :=
  Over.homMk (AlgebraicSpace.ofOverMap (ι[groupOver d])) sorry

/-- The underlying algebraic-space map of `inv d` is `ofOverMap` of the scheme-level inverse. -/
theorem inv_left (d : ℕ) [NeZero d] :
    (inv d).left = AlgebraicSpace.ofOverMap (ι[groupOver d]) :=
  sorry

/-- The multiplication morphism of `asOver d`. -/
def mul (d : ℕ) [NeZero d] : asOver d ⊗ asOver d ⟶ asOver d :=
  Over.homMk
    (spaceMul (fst (asOver d) (asOver d)).left (snd (asOver d) (asOver d)).left)
    sorry

/-- The underlying algebraic-space map of `mul d` multiplies the two projections. -/
theorem mul_left (d : ℕ) [NeZero d] :
    (mul d).left =
      spaceMul (fst (asOver d) (asOver d)).left (snd (asOver d) (asOver d)).left :=
  sorry

/-- The canonical group-object structure on `asOver d`. -/
instance instGrpObj_asOver (d : ℕ) [NeZero d] : GrpObj (asOver d) where
  one := one d
  mul := mul d
  inv := inv d
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry
  left_inv := sorry
  right_inv := sorry

/-- The unit-fixing closed subgroup of `GL_d` as a group algebraic space over `base`. -/
def groupSpace (d : ℕ) [NeZero d] : GroupAlgebraicSpace base :=
  ⟨asOver d⟩

/-- The underlying object of `groupSpace d` is `asOver d`. -/
theorem groupSpace_X (d : ℕ) [NeZero d] : (groupSpace d).X = asOver d :=
  sorry

/-- Identify `ofOver` of `GL_d` with `GeneralLinear.ofScheme specZ d`. -/
def toOfScheme (d : ℕ) [NeZero d] :
    AlgebraicSpace.ofOver (GeneralLinear.schemeOver (ULift.{u} ℤ) (ULift.{u} (Fin d))) ⟶
      AlgebraicSpace.GeneralLinear.ofScheme specZ d :=
  AlgebraicSpace.ofOverMap
    ((eqToIso
        (congrArg (fun f ↦ (Over.pullback f).obj
            (GeneralLinear.schemeOver (ULift.{u} ℤ) (ULift.{u} (Fin d))))
          (CategoryTheory.Limits.IsTerminal.from_self specULiftZIsTerminal))).trans
      (Over.pullbackId.app
        (GeneralLinear.schemeOver (ULift.{u} ℤ) (ULift.{u} (Fin d))))).inv

/-- `toOfScheme` is `ofOverMap` of the identity-pullback comparison. -/
theorem toOfScheme_eq (d : ℕ) [NeZero d] :
    toOfScheme d =
      AlgebraicSpace.ofOverMap
        ((eqToIso
            (congrArg (fun f ↦ (Over.pullback f).obj
                (GeneralLinear.schemeOver (ULift.{u} ℤ) (ULift.{u} (Fin d))))
              (CategoryTheory.Limits.IsTerminal.from_self specULiftZIsTerminal))).trans
          (Over.pullbackId.app
            (GeneralLinear.schemeOver (ULift.{u} ℤ) (ULift.{u} (Fin d))))).inv :=
  sorry

/-- The closed immersion of `groupSpace d` into `GL_d` over `base`. -/
def inclusion (d : ℕ) [NeZero d] :
    (groupSpace d).X ⟶ (AlgebraicSpace.GeneralLinear.groupSpace base d).X :=
  Over.homMk
    (AlgebraicSpace.productLift (AlgebraicSpace.toBase (space d))
      (AlgebraicSpace.ofOverMap (inclusionOver d) ≫ toOfScheme d))
    sorry

/-- The underlying algebraic-space map of `inclusion d` is the product lift of `toBase`
with the image of `inclusionOver`. -/
theorem inclusion_left (d : ℕ) [NeZero d] :
    (inclusion d).left =
      AlgebraicSpace.productLift (AlgebraicSpace.toBase (space d))
        (AlgebraicSpace.ofOverMap (inclusionOver d) ≫ toOfScheme d) :=
  sorry

/-- The inclusion `G ↪ GL_d` is a morphism of monoid objects. -/
theorem inclusion_isMonHom (d : ℕ) [NeZero d] : IsMonHom (inclusion d) :=
  sorry

/-- The inclusion `G ↪ GL_d` is a closed immersion of algebraic spaces. -/
instance instIsClosedImmersion_inclusion (d : ℕ) [NeZero d] :
    AlgebraicSpace.IsClosedImmersion (inclusion d).left :=
  sorry

/-- Morphisms over `base` into `groupSpace d` are multiplicatively equivalent to
unit-fixing automorphisms of `Fin d → Γ(T.left, ⊤)`. -/
def pointsMulEquiv (d : ℕ) [NeZero d] {T : Over specZ}
    (t : AlgebraicSpace.ofOver T ⟶ base) :
    (Over.mk t ⟶ (groupSpace d).X) ≃* glFixOne Γ(T.left, ⊤) d where
  toFun φ := homEquiv d T (yonedaEquiv φ.left)
  invFun g :=
    Over.homMk (AlgebraicSpace.ofOverMap ((homEquiv d T).symm g)) sorry
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry

/-- The forward map of `pointsMulEquiv` evaluates `homEquiv` on the underlying scheme
morphism. -/
theorem pointsMulEquiv_apply (d : ℕ) [NeZero d] {T : Over specZ}
    (t : AlgebraicSpace.ofOver T ⟶ base) (φ : Over.mk t ⟶ (groupSpace d).X) :
    pointsMulEquiv d t φ = homEquiv d T (yonedaEquiv φ.left) :=
  sorry

/-- The structure morphism of `space d` is smooth. -/
instance instSmooth_toBase (d : ℕ) [NeZero d] :
    AlgebraicSpace.Smooth (AlgebraicSpace.toBase (space d)) :=
  sorry

end AlgebraicGeometry.GLFixOne
