/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Equivalence
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import stacks_project.Chap85.Definition_85_12_1_Cartesian

/-!
# Face-descent data for cartesian sheaves on a simplicial site

Pairs `(F, α)` consisting of a sheaf on `C_0` and an isomorphism on `C_1` between the
two coface inverse images, together with the `C_2` cocycle.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites.Sheaf

/-- The last-vertex operator `τ^n_n : ⦋0⦌ ⟶ n`, sending `0` to `Fin.last n.len`. -/
def vertexOp (n : SimplexCategory) : ⦋0⦌ ⟶ n :=
  SimplexCategory.const ⦋0⦌ n (Fin.last n.len)

/-- `vertexOp n` is `SimplexCategory.const ⦋0⦌ n (Fin.last n.len)`. -/
theorem vertexOp_eq (n : SimplexCategory) :
    vertexOp n = SimplexCategory.const ⦋0⦌ n (Fin.last n.len) :=
  sorry

/-- The edge operator `τ^m_{φ(n)m} : ⦋1⦌ ⟶ m`, sending `0` to `φ (last n)` and `1` to
`last m`. -/
def edgeOp {n m : SimplexCategory} (φ : n ⟶ m) : ⦋1⦌ ⟶ m :=
  SimplexCategory.mkOfLe (φ.toOrderHom (Fin.last n.len)) (Fin.last m.len) (Fin.le_last _)

/-- `edgeOp φ` is `mkOfLe (φ (last n)) (last m)`. -/
theorem edgeOp_eq {n m : SimplexCategory} (φ : n ⟶ m) :
    edgeOp φ =
      SimplexCategory.mkOfLe (φ.toOrderHom (Fin.last n.len)) (Fin.last m.len)
        (Fin.le_last _) :=
  sorry

/-- `τ^n_n ≫ φ` agrees with `δ 1 ≫ τ^m_{φ(n)m}`. -/
theorem vertexOp_comp {n m : SimplexCategory} (φ : n ⟶ m) :
    vertexOp n ≫ φ = SimplexCategory.δ (1 : Fin 2) ≫ edgeOp φ :=
  sorry

/-- `δ 0 ≫ τ^m_{φ(n)m}` agrees with `τ^m_m`. -/
theorem edgeOp_comp_δ0 {n m : SimplexCategory} (φ : n ⟶ m) :
    SimplexCategory.δ (0 : Fin 2) ≫ edgeOp φ = vertexOp m :=
  sorry

/-- The last-vertex operator on `⦋0⦌` is the identity. -/
theorem vertexOp_zero : vertexOp ⦋0⦌ = 𝟙 ⦋0⦌ :=
  sorry

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instMorphismDiagram : IsMorphismDiagram C J]
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable (A : Type (w + 1)) [Category.{w} A]
variable [instWeakSheafifyA : ∀ n, HasWeakSheafify (J n).toGrothendieck A]
variable [instLeftKanA : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ A),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
include instMorphismDiagram instWeakSheafify instLeftKan instWeakSheafifyA instLeftKanA

/-- Inverse images along a composite simplex operator identify with the composite of
inverse images: `f_{ψ ≫ φ}⁻¹ ≅ f_ψ⁻¹ ⋙ f_φ⁻¹`. -/
def inverseImageCompIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    sheafInverseImage C J A (ψ ≫ φ) ≅
      sheafInverseImage C J A ψ ⋙ sheafInverseImage C J A φ :=
  (Functor.sheafPullbackComp' (J l).toGrothendieck (J m).toGrothendieck (J n).toGrothendieck
      (C.map ψ).toFunctor (C.map φ).toFunctor (map_comp_toFunctor C ψ φ)).symm

/-- `inverseImageCompIso` is the inverse of `sheafPullbackComp'` along `u_ψ` then `u_φ`. -/
theorem inverseImageCompIso_eq {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    inverseImageCompIso C J A ψ φ =
      (Functor.sheafPullbackComp' (J l).toGrothendieck (J m).toGrothendieck
          (J n).toGrothendieck (C.map ψ).toFunctor (C.map φ).toFunctor
          (map_comp_toFunctor C ψ φ)).symm :=
  sorry

/-- Reidentify `f_φ⁻¹` along an equality of simplex operators. -/
def recodeInverseImage {m n : SimplexCategory} {φ ψ : m ⟶ n} (h : φ = ψ) :
    sheafInverseImage C J A φ ≅ sheafInverseImage C J A ψ :=
  eqToIso (congrArg (fun t : m ⟶ n ↦ sheafInverseImage C J A t) h)

/-- `recodeInverseImage` is the identity when the operator equality is `rfl`. -/
theorem recodeInverseImage_refl {m n : SimplexCategory} (φ : m ⟶ n) :
    recodeInverseImage C J A (rfl : φ = φ) = Iso.refl _ :=
  sorry

/-- Inverse image along an identity simplex operator identifies with the identity functor. -/
def inverseImageIdIso (n : SimplexCategory) :
    sheafInverseImage C J A (𝟙 n) ≅ 𝟭 (Sheaf ((J n).toGrothendieck) A) :=
  Adjunction.leftAdjointIdIso
    ((C.map (𝟙 n)).toFunctor.sheafAdjunctionContinuous A
      (J n).toGrothendieck (J n).toGrothendieck)
    (Functor.sheafPushforwardContinuousId' (Cat.Hom.toNatIso (eqToIso (C.map_id n)))
      A (J n).toGrothendieck)

/-- `inverseImageIdIso` is left-adjoint uniqueness for the identity operator. -/
theorem inverseImageIdIso_eq (n : SimplexCategory) :
    inverseImageIdIso C J A n =
      Adjunction.leftAdjointIdIso
        ((C.map (𝟙 n)).toFunctor.sheafAdjunctionContinuous A
          (J n).toGrothendieck (J n).toGrothendieck)
        (Functor.sheafPushforwardContinuousId' (Cat.Hom.toNatIso (eqToIso (C.map_id n)))
          A (J n).toGrothendieck) :=
  sorry

/-- The pullback of `α` along a 2-face `δ i`, as a morphism of sheaves on `C_2`. -/
def facePullback (i : Fin 3) {F : Sheaf ((J ⦋0⦌).toGrothendieck) A}
    (α : (sheafInverseImage C J A (SimplexCategory.δ (1 : Fin 2))).obj F ≅
      (sheafInverseImage C J A (SimplexCategory.δ (0 : Fin 2))).obj F) :
    (sheafInverseImage C J A
        (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ i)).obj F ⟶
      (sheafInverseImage C J A
        (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ i)).obj F :=
  (inverseImageCompIso C J A (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ i)).hom.app
      F ≫
    (sheafInverseImage C J A (SimplexCategory.δ i)).map α.hom ≫
    (inverseImageCompIso C J A (SimplexCategory.δ (0 : Fin 2))
        (SimplexCategory.δ i)).inv.app F

/-- `facePullback i α` is `(f_{δ i})⁻¹ α` after the composition identifications. -/
theorem facePullback_eq (i : Fin 3) {F : Sheaf ((J ⦋0⦌).toGrothendieck) A}
    (α : (sheafInverseImage C J A (SimplexCategory.δ (1 : Fin 2))).obj F ≅
      (sheafInverseImage C J A (SimplexCategory.δ (0 : Fin 2))).obj F) :
    facePullback C J A i α =
      (inverseImageCompIso C J A (SimplexCategory.δ (1 : Fin 2))
          (SimplexCategory.δ i)).hom.app F ≫
        (sheafInverseImage C J A (SimplexCategory.δ i)).map α.hom ≫
        (inverseImageCompIso C J A (SimplexCategory.δ (0 : Fin 2))
            (SimplexCategory.δ i)).inv.app F :=
  sorry

/-- `(f_{δ 1})⁻¹ α` transported to a morphism out of `(f_{δ 1 ≫ δ 2})⁻¹ F`. -/
def cocycleLeft {F : Sheaf ((J ⦋0⦌).toGrothendieck) A}
    (α : (sheafInverseImage C J A (SimplexCategory.δ (1 : Fin 2))).obj F ≅
      (sheafInverseImage C J A (SimplexCategory.δ (0 : Fin 2))).obj F) :
    (sheafInverseImage C J A
        (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3))).obj F ⟶
      (sheafInverseImage C J A
        (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3))).obj F :=
  (recodeInverseImage C J A
        (SimplexCategory.δ_comp_δ_self (i := (1 : Fin 2))).symm).hom.app F ≫
    facePullback C J A 1 α

/-- `(f_{δ 0})⁻¹ α ∘ (f_{δ 2})⁻¹ α` after the `δ_comp_δ` identifications on `C_2`. -/
def cocycleRight {F : Sheaf ((J ⦋0⦌).toGrothendieck) A}
    (α : (sheafInverseImage C J A (SimplexCategory.δ (1 : Fin 2))).obj F ≅
      (sheafInverseImage C J A (SimplexCategory.δ (0 : Fin 2))).obj F) :
    (sheafInverseImage C J A
        (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3))).obj F ⟶
      (sheafInverseImage C J A
        (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3))).obj F :=
  facePullback C J A 2 α ≫
    (recodeInverseImage C J A
        (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2))
          (Fin.zero_le _))).hom.app F ≫
    facePullback C J A 0 α ≫
    (recodeInverseImage C J A
        (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (0 : Fin 2))
          le_rfl).symm).hom.app F

/-- `cocycleLeft` is `(f_{δ 1})⁻¹ α` after recoding along `δ_comp_δ_self`. -/
theorem cocycleLeft_eq {F : Sheaf ((J ⦋0⦌).toGrothendieck) A}
    (α : (sheafInverseImage C J A (SimplexCategory.δ (1 : Fin 2))).obj F ≅
      (sheafInverseImage C J A (SimplexCategory.δ (0 : Fin 2))).obj F) :
    cocycleLeft C J A α =
      (recodeInverseImage C J A
          (SimplexCategory.δ_comp_δ_self (i := (1 : Fin 2))).symm).hom.app F ≫
        facePullback C J A 1 α :=
  sorry

/-- `cocycleRight` is `(f_{δ 0})⁻¹ α ∘ (f_{δ 2})⁻¹ α` after the `δ_comp_δ` identifications. -/
theorem cocycleRight_eq {F : Sheaf ((J ⦋0⦌).toGrothendieck) A}
    (α : (sheafInverseImage C J A (SimplexCategory.δ (1 : Fin 2))).obj F ≅
      (sheafInverseImage C J A (SimplexCategory.δ (0 : Fin 2))).obj F) :
    cocycleRight C J A α =
      facePullback C J A 2 α ≫
        (recodeInverseImage C J A
            (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2))
              (Fin.zero_le _))).hom.app F ≫
        facePullback C J A 0 α ≫
        (recodeInverseImage C J A
            (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (0 : Fin 2))
              le_rfl).symm).hom.app F :=
  sorry

/-- A pair `(F, α)` with `F` a sheaf on `C_0` and `α : (f_{δ 1})⁻¹ F ≅ (f_{δ 0})⁻¹ F` on
`C_1` satisfying the `C_2` cocycle `(f_{δ 1})⁻¹ α = (f_{δ 0})⁻¹ α ∘ (f_{δ 2})⁻¹ α`. -/
structure FaceDescent where
  /-- The sheaf `F` on `C_0`. -/
  sheaf : Sheaf ((J ⦋0⦌).toGrothendieck) A
  /-- The isomorphism `α : (f_{δ 1})⁻¹ F ≅ (f_{δ 0})⁻¹ F` of sheaves on `C_1`. -/
  iso :
    (sheafInverseImage C J A (SimplexCategory.δ (1 : Fin 2))).obj sheaf ≅
      (sheafInverseImage C J A (SimplexCategory.δ (0 : Fin 2))).obj sheaf
  /-- The cocycle `(f_{δ 1})⁻¹ α = (f_{δ 0})⁻¹ α ∘ (f_{δ 2})⁻¹ α` on `C_2`. -/
  cocycle : cocycleLeft C J A iso = cocycleRight C J A iso

namespace FaceDescent

variable {C J A}

/-- Build face-descent data from a sheaf on `C_0`, a coface isomorphism on `C_1`, and the
cocycle proof. -/
def ofIso (F : Sheaf ((J ⦋0⦌).toGrothendieck) A)
    (α : (sheafInverseImage C J A (SimplexCategory.δ (1 : Fin 2))).obj F ≅
      (sheafInverseImage C J A (SimplexCategory.δ (0 : Fin 2))).obj F)
    (hcocycle : cocycleLeft C J A α = cocycleRight C J A α) :
    FaceDescent C J A where
  sheaf := F
  iso := α
  cocycle := hcocycle

/-- The defining cocycle of a face-descent pair. -/
theorem spec (D : FaceDescent C J A) :
    cocycleLeft C J A D.iso = cocycleRight C J A D.iso :=
  sorry

/-- A morphism of face-descent pairs is a map of the underlying sheaves on `C_0` commuting
with `α`. -/
structure Hom (D E : FaceDescent C J A) where
  /-- The underlying morphism of sheaves on `C_0`. -/
  hom : D.sheaf ⟶ E.sheaf
  /-- Commutation with the coface isomorphisms on `C_1`. -/
  comm :
    (sheafInverseImage C J A (SimplexCategory.δ (1 : Fin 2))).map hom ≫ E.iso.hom =
      D.iso.hom ≫ (sheafInverseImage C J A (SimplexCategory.δ (0 : Fin 2))).map hom

/-- Build a morphism of face-descent pairs from a sheaf map commuting with `α`. -/
def homMk {D E : FaceDescent C J A} (f : D.sheaf ⟶ E.sheaf)
    (comm :
      (sheafInverseImage C J A (SimplexCategory.δ (1 : Fin 2))).map f ≫ E.iso.hom =
        D.iso.hom ≫ (sheafInverseImage C J A (SimplexCategory.δ (0 : Fin 2))).map f) :
    Hom D E where
  hom := f
  comm := comm

/-- The identity morphism of face-descent pairs. -/
def Hom.id (D : FaceDescent C J A) : Hom D D :=
  homMk (𝟙 D.sheaf) sorry

/-- Composition of morphisms of face-descent pairs. -/
def Hom.comp {D E F : FaceDescent C J A} (f : Hom D E) (g : Hom E F) : Hom D F :=
  homMk (f.hom ≫ g.hom) sorry

/-- The underlying sheaf morphism of `homMk f comm` is `f`. -/
theorem homMk_hom {D E : FaceDescent C J A} (f : D.sheaf ⟶ E.sheaf)
    (comm :
      (sheafInverseImage C J A (SimplexCategory.δ (1 : Fin 2))).map f ≫ E.iso.hom =
        D.iso.hom ≫ (sheafInverseImage C J A (SimplexCategory.δ (0 : Fin 2))).map f) :
    (homMk f comm).hom = f :=
  sorry

/-- The category of pairs `(F, α)` on the simplicial site `(C, J)` with coefficients in `A`. -/
instance category : Category (FaceDescent C J A) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The reconstructed comparison `G(φ) : (f_φ)⁻¹ G_n ⟶ G_m` attached to a pair `(F, α)`. -/
def transitionOf {n m : SimplexCategory} (φ : n ⟶ m) (D : FaceDescent C J A) :
    (sheafInverseImage C J A φ).obj
        ((sheafInverseImage C J A (vertexOp n)).obj D.sheaf) ⟶
      (sheafInverseImage C J A (vertexOp m)).obj D.sheaf :=
  (inverseImageCompIso C J A (vertexOp n) φ).inv.app D.sheaf ≫
    (recodeInverseImage C J A
        (SimplexCategory.Hom.ext_zero_left (vertexOp n ≫ φ)
          (SimplexCategory.δ (1 : Fin 2) ≫ edgeOp φ))).hom.app D.sheaf ≫
    (inverseImageCompIso C J A (SimplexCategory.δ (1 : Fin 2)) (edgeOp φ)).hom.app
      D.sheaf ≫
    (sheafInverseImage C J A (edgeOp φ)).map D.iso.hom ≫
    (inverseImageCompIso C J A (SimplexCategory.δ (0 : Fin 2)) (edgeOp φ)).inv.app
      D.sheaf ≫
    (recodeInverseImage C J A
        (SimplexCategory.Hom.ext_zero_left
          (SimplexCategory.δ (0 : Fin 2) ≫ edgeOp φ) (vertexOp m))).hom.app D.sheaf

/-- `transitionOf φ D` is the source diagram for `G(φ)`, obtained by recoding along
`τ^n_n ≫ φ = τ^m_{φ(n)}` and applying `(f_{τ^m_{φ(n)m}})⁻¹ α`. -/
theorem transitionOf_eq {n m : SimplexCategory} (φ : n ⟶ m) (D : FaceDescent C J A) :
    transitionOf φ D =
      (inverseImageCompIso C J A (vertexOp n) φ).inv.app D.sheaf ≫
        (recodeInverseImage C J A
            (SimplexCategory.Hom.ext_zero_left (vertexOp n ≫ φ)
              (SimplexCategory.δ (1 : Fin 2) ≫ edgeOp φ))).hom.app D.sheaf ≫
        (inverseImageCompIso C J A (SimplexCategory.δ (1 : Fin 2))
            (edgeOp φ)).hom.app D.sheaf ≫
        (sheafInverseImage C J A (edgeOp φ)).map D.iso.hom ≫
        (inverseImageCompIso C J A (SimplexCategory.δ (0 : Fin 2))
            (edgeOp φ)).inv.app D.sheaf ≫
        (recodeInverseImage C J A
            (SimplexCategory.Hom.ext_zero_left
              (SimplexCategory.δ (0 : Fin 2) ≫ edgeOp φ) (vertexOp m))).hom.app D.sheaf :=
  sorry

/-- The identity morphism of face-descent pairs is the identity on the underlying sheaf. -/
theorem Hom.id_hom (D : FaceDescent C J A) : (Hom.id D).hom = 𝟙 D.sheaf :=
  sorry

/-- Composition of face-descent pairs is composition of the underlying sheaf morphisms. -/
theorem Hom.comp_hom {D E F : FaceDescent C J A} (f : Hom D E) (g : Hom E F) :
    (Hom.comp f g).hom = f.hom ≫ g.hom :=
  sorry

end FaceDescent

end CategoryTheory.SimplicialSites.Sheaf
