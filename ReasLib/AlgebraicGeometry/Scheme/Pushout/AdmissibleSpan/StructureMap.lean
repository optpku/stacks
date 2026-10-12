/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Pushout.AdmissibleSpan.Existence

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan

/-- The canonical structure morphism from the pushout of an admissible span to its base. -/
noncomputable def toBase {S : Scheme.{u}} {Z X Y : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y) [IsAdmissibleSpan i j] :
    pushout i.left j.left ⟶ S :=
  pushout.desc X.hom Y.hom (i.w.trans j.w.symm)

/-- The first pushout inclusion followed by the canonical structure morphism is `X.hom`. -/
theorem inl_toBase {S : Scheme.{u}} {Z X Y : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y) [IsAdmissibleSpan i j] :
    pushout.inl i.left j.left ≫ toBase i j = X.hom := sorry

/-- The second pushout inclusion followed by the canonical structure morphism is `Y.hom`. -/
theorem inr_toBase {S : Scheme.{u}} {Z X Y : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y) [IsAdmissibleSpan i j] :
    pushout.inr i.left j.left ≫ toBase i j = Y.hom := sorry

/-- The canonical morphism from `Y.left ⨿ X.left` to the pushout, followed by the
structure morphism, is the coproduct of the two original structure morphisms. -/
theorem coprodDesc_toBase {S : Scheme.{u}} {Z X Y : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y) [IsAdmissibleSpan i j] :
    coprod.desc (pushout.inr i.left j.left) (pushout.inl i.left j.left) ≫ toBase i j =
      coprod.desc Y.hom X.hom := sorry

end AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan
