/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Correspondence.Chow
public import ReasLib.AlgebraicGeometry.Correspondence.Graded
public import ReasLib.AlgebraicGeometry.Correspondence.Graph
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Finite

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Correspondence

variable {k : Type u} [Field k]

/-- Smooth-projective correspondence objects equipped with an integral Tate index. -/
def TateGraded (k : Type u) [Field k] : Type (u + 1) := Graded k × ℤ

namespace TateGraded

/-- The field point is projective over the ground field. -/
instance point_projective : Projective (SchemeOverField.point k).hom := inferInstance

/-- Place a smooth-projective scheme in a specified integral Tate degree. -/
def ofScheme (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    (n : ℤ) : TateGraded k := (Graded.of X inferInstance inferInstance, n)

/-- The identity-degree arithmetic for Tate-graded correspondences. -/
theorem degree_id (n : ℤ) : 0 = n - n := by omega

/-- The composition-degree arithmetic for Tate-graded correspondences. -/
theorem degree_comp (a b c : ℤ) : (b - a) + (c - b) = c - a := by omega

/-- The identity correspondence in a specified Tate degree. -/
def idHom (X : TateGraded k) : Rational X.1.scheme X.1.scheme (X.2 - X.2) :=
  castDegree (degree_id X.2) (rationalGraph (𝟙 X.1.scheme))

/-- Composition of homogeneous rational correspondences with degree transport. -/
def compHom {X Y Z : TateGraded k} (f : Rational X.1.scheme Y.1.scheme (Y.2 - X.2))
    (g : Rational Y.1.scheme Z.1.scheme (Z.2 - Y.2)) :
    Rational X.1.scheme Z.1.scheme (Z.2 - X.2) :=
  castDegree (degree_comp X.2 Y.2 Z.2)
    (composition X.1.scheme Y.1.scheme Z.1.scheme (Y.2 - X.2) (Z.2 - Y.2) f g)

private theorem castDegree_eq_transport {X Y : SchemeOverField k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {r s : ℤ} (h : r = s) (c : Rational X Y r) : castDegree h c = h ▸ c := by
  cases h
  letI := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (CategoryTheory.Limits.prod.snd : X ⨯ Y ⟶ Y) r
  change castDegree (rfl : r = r) c = c
  induction c using TensorProduct.induction_on with
  | zero => exact (castDegree rfl).map_zero
  | tmul a c => simp [castDegree, BivariantClass.Nonnegative.castGrading]
  | add c d hc hd => simp only [map_add, hc, hd]

private theorem castDegree_trans {X Y : SchemeOverField k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {r s t : ℤ} (h : r = s) (h' : s = t) (c : Rational X Y r) :
    castDegree h' (castDegree h c) = castDegree (h.trans h') c := by
  cases h
  cases h'
  simp only [castDegree_eq_transport]

private theorem composition_castDegree {X Y Z : SchemeOverField k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] [Projective Y.hom]
    {r r' s s' : ℤ} (hr : r = r') (hs : s = s')
    (f : Rational X Y r) (g : Rational Y Z s) :
    composition X Y Z r' s' (castDegree hr f) (castDegree hs g) =
      castDegree (congrArg₂ (· + ·) hr hs) (composition X Y Z r s f g) := by
  cases hr
  cases hs
  simp only [castDegree_eq_transport]

/-- Composition of Tate-graded correspondences is associative. -/
theorem assoc {W X Y Z : TateGraded k}
    (f : Rational W.1.scheme X.1.scheme (X.2 - W.2))
    (g : Rational X.1.scheme Y.1.scheme (Y.2 - X.2))
    (h : Rational Y.1.scheme Z.1.scheme (Z.2 - Y.2)) :
    compHom (compHom f g) h = compHom f (compHom g h) := by
  unfold compHom
  have hleft :=
    composition_castDegree (X := W.1.scheme) (Y := Y.1.scheme) (Z := Z.1.scheme)
      (hr := degree_comp W.2 X.2 Y.2) (hs := (rfl : Z.2 - Y.2 = Z.2 - Y.2))
      (f := composition W.1.scheme X.1.scheme Y.1.scheme
        (X.2 - W.2) (Y.2 - X.2) f g) (g := h)
  have hright :=
    composition_castDegree (X := W.1.scheme) (Y := X.1.scheme) (Z := Z.1.scheme)
      (hr := (rfl : X.2 - W.2 = X.2 - W.2))
      (hs := degree_comp X.2 Y.2 Z.2) (f := f)
      (g := composition X.1.scheme Y.1.scheme Z.1.scheme
        (Y.2 - X.2) (Z.2 - Y.2) g h)
  rw [show
    composition W.1.scheme Y.1.scheme Z.1.scheme (Y.2 - W.2) (Z.2 - Y.2)
        (castDegree (degree_comp W.2 X.2 Y.2)
          (composition W.1.scheme X.1.scheme Y.1.scheme
            (X.2 - W.2) (Y.2 - X.2) f g)) h =
      castDegree (congrArg₂ (· + ·) (degree_comp W.2 X.2 Y.2)
        (rfl : Z.2 - Y.2 = Z.2 - Y.2))
        (composition W.1.scheme Y.1.scheme Z.1.scheme
          ((X.2 - W.2) + (Y.2 - X.2)) (Z.2 - Y.2)
          (composition W.1.scheme X.1.scheme Y.1.scheme
            (X.2 - W.2) (Y.2 - X.2) f g) h) by
      simpa only [castDegree_eq_transport] using hleft]
  rw [castDegree_trans]
  have houter :
      (X.2 - W.2) + ((Y.2 - X.2) + (Z.2 - Y.2)) = Z.2 - W.2 := by
    omega
  rw [← castDegree_trans (h := add_assoc (X.2 - W.2) (Y.2 - X.2) (Z.2 - Y.2))
    (h' := houter)]
  rw [AlgebraicGeometry.Correspondence.composition_assoc]
  rw [show
    composition W.1.scheme X.1.scheme Z.1.scheme (X.2 - W.2) (Z.2 - X.2) f
        (castDegree (degree_comp X.2 Y.2 Z.2)
          (composition X.1.scheme Y.1.scheme Z.1.scheme
            (Y.2 - X.2) (Z.2 - Y.2) g h)) =
      castDegree (congrArg₂ (· + ·) (rfl : X.2 - W.2 = X.2 - W.2)
        (degree_comp X.2 Y.2 Z.2))
        (composition W.1.scheme X.1.scheme Z.1.scheme
          (X.2 - W.2) ((Y.2 - X.2) + (Z.2 - Y.2)) f
          (composition X.1.scheme Y.1.scheme Z.1.scheme
            (Y.2 - X.2) (Z.2 - Y.2) g h)) by
      simpa only [castDegree_eq_transport] using hright]
  rw [castDegree_trans]

/-- Composition with the identity correspondence on the source is trivial. -/
theorem id_comp {X Y : TateGraded k}
    (f : Rational X.1.scheme Y.1.scheme (Y.2 - X.2)) :
    compHom (idHom X) f = f := sorry

/-- Composition with the identity correspondence on the target is trivial. -/
theorem comp_id {X Y : TateGraded k}
    (f : Rational X.1.scheme Y.1.scheme (Y.2 - X.2)) :
    compHom f (idHom Y) = f := sorry

/-- Composition distributes over addition in the first variable. -/
theorem add_comp (X Y Z : TateGraded k)
    (f g : Rational X.1.scheme Y.1.scheme (Y.2 - X.2))
    (h : Rational Y.1.scheme Z.1.scheme (Z.2 - Y.2)) :
    compHom (f + g) h = compHom f h + compHom g h := by
  simp [compHom]

/-- Composition distributes over addition in the second variable. -/
theorem comp_add (X Y Z : TateGraded k)
    (f : Rational X.1.scheme Y.1.scheme (Y.2 - X.2))
    (g h : Rational Y.1.scheme Z.1.scheme (Z.2 - Y.2)) :
    compHom f (g + h) = compHom f g + compHom f h := by
  simp [compHom]

/-- Rational scalar multiplication commutes with composition in the first variable. -/
theorem smul_comp (X Y Z : TateGraded k) (r : ℚ)
    (f : Rational X.1.scheme Y.1.scheme (Y.2 - X.2))
    (g : Rational Y.1.scheme Z.1.scheme (Z.2 - Y.2)) :
    compHom (r • f) g = r • compHom f g := by
  simp [compHom]

/-- Rational scalar multiplication commutes with composition in the second variable. -/
theorem comp_smul (X Y Z : TateGraded k)
    (f : Rational X.1.scheme Y.1.scheme (Y.2 - X.2)) (r : ℚ)
    (g : Rational Y.1.scheme Z.1.scheme (Z.2 - Y.2)) :
    compHom f (r • g) = r • compHom f g := by
  simp [compHom]

/-- Tate-graded correspondences form a category by composing rational correspondences. -/
@[reducible]
def category : Category (TateGraded k) where
  Hom X Y := Rational X.1.scheme Y.1.scheme (Y.2 - X.2)
  id := idHom
  comp := compHom
  assoc := TateGraded.assoc
  id_comp := TateGraded.id_comp
  comp_id := TateGraded.comp_id

/-- The canonical category structure on Tate-graded correspondences. -/
instance instCategory : Category (TateGraded k) := category

/-- The Tate-graded correspondence category is preadditive. -/
instance instPreadditive : Preadditive (TateGraded k) where
  homGroup X Y :=
    inferInstanceAs (AddCommGroup (Rational X.1.scheme Y.1.scheme (Y.2 - X.2)))
  add_comp := TateGraded.add_comp
  comp_add := TateGraded.comp_add

/-- The Tate-graded correspondence category is rational-linear. -/
instance instLinear : Linear ℚ (TateGraded k) where
  homModule X Y :=
    inferInstanceAs (Module ℚ (Rational X.1.scheme Y.1.scheme (Y.2 - X.2)))
  smul_comp := TateGraded.smul_comp
  comp_smul := TateGraded.comp_smul

end TateGraded

end AlgebraicGeometry.Correspondence
