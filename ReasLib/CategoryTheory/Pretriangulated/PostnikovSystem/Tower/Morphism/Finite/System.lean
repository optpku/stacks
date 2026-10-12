/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Morphism.Triangle
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Morphism.Finite.Row
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Morphism.Triangle

/-!
# Finite-System Restrictions of Postnikov-Tower Morphisms

This leaf restricts a tower morphism to the canonical finite Postnikov systems
and exposes clean recursive and pointwise component computations.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Tower.Hom

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {T T' T'' : Tower D}

namespace Core

/-- Internal auxiliary-object components of finite restriction, synchronized with
`Tower.Core.build`. -/
def finiteYMap (f : Hom T T') :
    (n : ℕ) → ∀ i : Fin (n + 1), T.finite n i ⟶ T'.finite n i
  | 0 => fun i => Fin.cases (f.yMap 0) (fun j => Fin.elim0 j) i
  | n + 1 => fun i => Fin.cases (f.yMap (n + 1)) (finiteYMap f n) i

/-- Internal finite auxiliary maps commute with the comparisons to the finite row. -/
theorem finiteYMap_comm_toX (f : Hom T T') (n : ℕ) (i : Fin (n + 1)) :
    CommSq ((T.finite n).toX i) (finiteYMap f n i) ((row f n).app i)
      ((T'.finite n).toX i) := sorry

/-- Internal finite auxiliary maps commute with the second maps of stage triangles. -/
theorem finiteYMap_comm_toNext (f : Hom T T') (n : ℕ) (i : Fin n) :
    CommSq ((T.finite n).toNext i) ((row f n).app i.castSucc)
      (finiteYMap f n i.succ) ((T'.finite n).toNext i) := sorry

/-- Internal finite auxiliary maps commute with the connecting maps of stage triangles. -/
theorem finiteYMap_comm_connecting (f : Hom T T') (n : ℕ) (i : Fin n) :
    CommSq ((T.finite n).connecting i) (finiteYMap f n i.succ)
      ((finiteYMap f n i.castSucc)⟦(1 : ℤ)⟧') ((T'.finite n).connecting i) := sorry

end Core

/-- Restrict a tower morphism to a morphism of the induced finite Postnikov systems. -/
@[stacks 0D8Z "finite restriction of a Postnikov tower morphism"]
def finite (f : Hom T T') (n : ℕ) :
    PostnikovSystem.Morphism (T.finite n) (T'.finite n) (row f n) where
  yMap := Core.finiteYMap f n
  comm_toX := Core.finiteYMap_comm_toX f n
  comm_toNext := Core.finiteYMap_comm_toNext f n
  comm_connecting := Core.finiteYMap_comm_connecting f n

/-- At length zero, finite restriction uses the zeroth auxiliary-object component. -/
@[simp 1100]
theorem finite_zero_yMap (f : Hom T T') :
    (finite f 0).yMap 0 = f.yMap 0 := sorry

/-- The new head of a successor finite restriction uses the corresponding auxiliary map. -/
@[simp 1100]
theorem finite_succ_yMap_zero (f : Hom T T') (n : ℕ) :
    (finite f (n + 1)).yMap 0 = f.yMap (n + 1) := sorry

/-- Successor components of a successor finite restriction come from the preceding restriction. -/
@[simp 1100]
theorem finite_succ_yMap_succ (f : Hom T T') (n : ℕ) (i : Fin (n + 1)) :
    (finite f (n + 1)).yMap i.succ = (finite f n).yMap i := sorry

/-- An auxiliary component of finite restriction is the corresponding transported `yMap`. This
theorem is intentionally not a simp rule because its normal form contains endpoint transports. -/
@[stacks 0D8Z]
theorem finite_yMap (f : Hom T T') (n : ℕ) (i : Fin (n + 1)) :
    (finite f n).yMap i =
      eqToHom (Tower.Finite.auxObj T n i) ≫ f.yMap (Tower.Finite.index i) ≫
        eqToHom (Tower.Finite.auxObj T' n i).symm := sorry

/-- The stage-triangle morphism of a finite restriction is the corresponding tower
stage-triangle morphism, transported along the canonical finite-stage identifications. This
theorem is intentionally not a simp rule because its normal form contains endpoint transports. -/
@[stacks 0D8Z "stage-triangle morphism of a finite Postnikov-tower restriction"]
theorem finite_triangleMorphism (f : Hom T T') (n : ℕ) (i : Fin n) :
    (finite f n).triangleMorphism i =
      eqToHom (Tower.Finite.triangle T n i) ≫
        triangleMorphism f (Tower.Finite.index i) ≫
          eqToHom (Tower.Finite.triangle T' n i).symm := sorry

/-- Finite restriction of an identity is componentwise the identity on auxiliary objects. -/
@[simp]
theorem id_finite_yMap (T : Tower D) (n : ℕ) (i : Fin (n + 1)) :
    (finite (id T) n).yMap i = 𝟙 (T.finite n i) := sorry

/-- Finite restriction of a composite composes auxiliary-object components pointwise. -/
@[simp]
theorem comp_finite_yMap (f : Hom T T') (g : Hom T' T'') (n : ℕ)
    (i : Fin (n + 1)) :
    (finite (comp f g) n).yMap i = (finite f n).yMap i ≫ (finite g n).yMap i := sorry

end CategoryTheory.PostnikovSystem.Tower.Hom
