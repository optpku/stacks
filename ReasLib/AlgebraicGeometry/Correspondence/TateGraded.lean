/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

/-- Composition of Tate-graded correspondences is associative. -/
theorem assoc {W X Y Z : TateGraded k}
    (f : Rational W.1.scheme X.1.scheme (X.2 - W.2))
    (g : Rational X.1.scheme Y.1.scheme (Y.2 - X.2))
    (h : Rational Y.1.scheme Z.1.scheme (Z.2 - Y.2)) :
    compHom (compHom f g) h = compHom f (compHom g h) := sorry

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
    compHom (f + g) h = compHom f h + compHom g h := sorry

/-- Composition distributes over addition in the second variable. -/
theorem comp_add (X Y Z : TateGraded k)
    (f : Rational X.1.scheme Y.1.scheme (Y.2 - X.2))
    (g h : Rational Y.1.scheme Z.1.scheme (Z.2 - Y.2)) :
    compHom f (g + h) = compHom f g + compHom f h := sorry

/-- Rational scalar multiplication commutes with composition in the first variable. -/
theorem smul_comp (X Y Z : TateGraded k) (r : ℚ)
    (f : Rational X.1.scheme Y.1.scheme (Y.2 - X.2))
    (g : Rational Y.1.scheme Z.1.scheme (Z.2 - Y.2)) :
    compHom (r • f) g = r • compHom f g := sorry

/-- Rational scalar multiplication commutes with composition in the second variable. -/
theorem comp_smul (X Y Z : TateGraded k)
    (f : Rational X.1.scheme Y.1.scheme (Y.2 - X.2)) (r : ℚ)
    (g : Rational Y.1.scheme Z.1.scheme (Z.2 - Y.2)) :
    compHom f (r • g) = r • compHom f g := sorry

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
