module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic
public import ReasLib.CategoryTheory.Fibered.InheritedTopology

/-!
# The polynomial site `C_{X/Λ}` of a scheme over a ring

Objects of `C_{X/Λ}` are morphisms `U ⟶ Spec(Λ[vars])` over `Spec Λ`, with `U` an
object of the small Zariski site of the `Λ`-scheme `X`.  The forgetful functor
`u : C_{X/Λ} ⥤ X_Zar` inherits the Zariski topology.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CotangentSite

variable (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]

/-- Affine space presented as `Spec` of a polynomial `Λ`-algebra. -/
abbrev specPolynomial (σ : Type u) : Scheme.{u} :=
  Spec (CommRingCat.of (MvPolynomial σ Λ))

/-- The structure morphism `Spec(Λ[σ]) ⟶ Spec Λ`. -/
abbrev specPolynomialToBase (σ : Type u) : specPolynomial Λ σ ⟶ Spec Λ :=
  Spec.map (CommRingCat.ofHom (C : Λ →+* MvPolynomial σ Λ))

/-- Affine space `Spec(Λ[σ])` is a scheme over `Spec Λ`. -/
instance specPolynomial_over (σ : Type u) : (specPolynomial Λ σ).Over (Spec Λ) :=
  ⟨specPolynomialToBase Λ σ⟩

/-- An open immersion into the `Λ`-scheme `X` is a scheme over `Spec Λ`. -/
instance open_over (U : X.smallZariskiSite) : U.left.Over (Spec Λ) :=
  ⟨U.hom ≫ X ↘ Spec Λ⟩

/-- An object of `C_{X/Λ}`: an open immersion `U ⟶ X` together with a morphism
to an affine space `Spec(Λ[vars])` over `Spec Λ`. -/
structure Obj where
  /-- The object of the small Zariski site of `X`. -/
  U : X.smallZariskiSite
  /-- The index type of polynomial variables. -/
  vars : Type u
  /-- The morphism from the open to affine space over `Spec Λ`. -/
  hom : U.left ⟶ specPolynomial Λ vars
  /-- The square over `Spec Λ` commutes. -/
  w : hom ≫ specPolynomialToBase Λ vars = U.hom ≫ X ↘ Spec Λ

namespace Obj

variable {Λ X}

/-- Package an open of `X_Zar`, a variable type, and a morphism to `Spec(Λ[vars])`
over `Spec Λ` as an object of `C_{X/Λ}`. -/
def of (U : X.smallZariskiSite) (vars : Type u)
    (hom : U.left ⟶ specPolynomial Λ vars)
    (w : hom ≫ specPolynomialToBase Λ vars = U.hom ≫ X ↘ Spec Λ) : Obj Λ X where
  U := U
  vars := vars
  hom := hom
  w := w

/-- The open of `of U vars hom w` is `U`. -/
theorem of_U (U : X.smallZariskiSite) (vars : Type u)
    (hom : U.left ⟶ specPolynomial Λ vars)
    (w : hom ≫ specPolynomialToBase Λ vars = U.hom ≫ X ↘ Spec Λ) :
    (of U vars hom w).U = U :=
  sorry

/-- The variable type of `of U vars hom w` is `vars`. -/
theorem of_vars (U : X.smallZariskiSite) (vars : Type u)
    (hom : U.left ⟶ specPolynomial Λ vars)
    (w : hom ≫ specPolynomialToBase Λ vars = U.hom ≫ X ↘ Spec Λ) :
    (of U vars hom w).vars = vars :=
  sorry

/-- The affine-space morphism of `of U vars hom w` is `hom`. -/
theorem of_hom (U : X.smallZariskiSite) (vars : Type u)
    (hom : U.left ⟶ specPolynomial Λ vars)
    (w : hom ≫ specPolynomialToBase Λ vars = U.hom ≫ X ↘ Spec Λ) :
    (of U vars hom w).hom = hom :=
  sorry

/-- The affine-space vertex `A = Spec(Λ[P.vars])` of an object of `C_{X/Λ}`. -/
abbrev A (P : Obj Λ X) : Scheme.{u} := specPolynomial Λ P.vars

end Obj

variable {Λ X}

/-- A morphism of `C_{X/Λ}` is a commutative square of maps of opens and of
affine spaces over `Spec Λ`. -/
structure Hom (P Q : Obj Λ X) where
  /-- The morphism of objects of `X_Zar`. -/
  left : P.U ⟶ Q.U
  /-- The morphism of affine spaces. -/
  right : P.A ⟶ Q.A
  /-- The affine-space map lies over `Spec Λ`. -/
  isOver : right ≫ specPolynomialToBase Λ Q.vars = specPolynomialToBase Λ P.vars
  /-- The square `U ⟶ A` commutes. -/
  w : P.hom ≫ right = left.left ≫ Q.hom

namespace Hom

/-- A morphism of `C_{X/Λ}` is a map of opens, a map of affine spaces over `Spec Λ`,
and a commuting square. -/
theorem spec {P Q : Obj Λ X} (f : Hom P Q) :
    f.right ≫ specPolynomialToBase Λ Q.vars = specPolynomialToBase Λ P.vars ∧
      P.hom ≫ f.right = f.left.left ≫ Q.hom :=
  sorry

/-- The identity morphism of an object of `C_{X/Λ}`. -/
def id (P : Obj Λ X) : Hom P P where
  left := 𝟙 P.U
  right := 𝟙 P.A
  isOver := sorry
  w := sorry

/-- Composition of morphisms of `C_{X/Λ}`. -/
def comp {P Q R : Obj Λ X} (f : Hom P Q) (g : Hom Q R) : Hom P R where
  left := f.left ≫ g.left
  right := f.right ≫ g.right
  isOver := sorry
  w := sorry

/-- Left identity law for morphisms of `C_{X/Λ}`. -/
theorem id_comp {P Q : Obj Λ X} (f : Hom P Q) : Hom.comp (Hom.id P) f = f :=
  sorry

/-- Right identity law for morphisms of `C_{X/Λ}`. -/
theorem comp_id {P Q : Obj Λ X} (f : Hom P Q) : Hom.comp f (Hom.id Q) = f :=
  sorry

/-- Associativity of composition of morphisms of `C_{X/Λ}`. -/
theorem assoc {P Q R S : Obj Λ X} (f : Hom P Q) (g : Hom Q R) (h : Hom R S) :
    Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h) :=
  sorry

end Hom

variable (Λ X)

/-- Morphisms of `C_{X/Λ}` form a category. -/
instance : Category.{u} (Obj Λ X) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- The forgetful functor `u : C_{X/Λ} ⥤ X_Zar`, sending `(U ⟶ A)` to `U`. -/
def forgetZariski : Obj Λ X ⥤ X.smallZariskiSite where
  obj P := P.U
  map {P Q} f := (f : Hom P Q).left
  map_id := sorry
  map_comp := sorry

/-- The forgetful functor of `C_{X/Λ}` sends an object to its open. -/
theorem forgetZariski_obj (P : Obj Λ X) : (forgetZariski Λ X).obj P = P.U :=
  sorry

/-- Identity morphisms of `C_{X/Λ}` act as identities on `X_Zar`. -/
theorem forgetZariski_map_id (P : Obj Λ X) :
    (forgetZariski Λ X).map (𝟙 P) = 𝟙 P.U :=
  sorry

/-- Composition of morphisms of `C_{X/Λ}` is composition in `X_Zar` on opens. -/
theorem forgetZariski_map_comp {P Q R : Obj Λ X} (f : P ⟶ Q) (g : Q ⟶ R) :
    (forgetZariski Λ X).map (f ≫ g) =
      (forgetZariski Λ X).map f ≫ (forgetZariski Λ X).map g :=
  sorry

/-- The Grothendieck topology on `C_{X/Λ}` inherited from `X_Zar`. -/
abbrev topology : GrothendieckTopology (Obj Λ X) :=
  (forgetZariski Λ X).inheritedTopology X.smallZariskiTopology

/-- The forgetful functor `u` is cocontinuous for the inherited topology. -/
instance forgetZariski_isCocontinuous :
    (forgetZariski Λ X).IsCocontinuous (topology Λ X) X.smallZariskiTopology :=
  sorry

end AlgebraicGeometry.Scheme.CotangentSite
