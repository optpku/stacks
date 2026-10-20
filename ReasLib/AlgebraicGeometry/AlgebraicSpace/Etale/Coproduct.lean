module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Coproduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale

/-!
# Étale morphisms and coproducts of algebraic spaces

Binary coproduct families have explicit structure morphisms. Coproduct inclusions
and coproducts of étale morphisms are étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The `Fin 2`-indexed family with values `U1` and `U2`. -/
def finTwo (U1 U2 : AlgebraicSpace S) (i : Fin 2) : AlgebraicSpace S :=
  match i with
  | 0 => U1
  | 1 => U2

/-- The `Fin 2`-indexed family of morphisms `f1, f2` into `X`. -/
def finTwoHom {X U1 U2 : AlgebraicSpace S} (f1 : U1 ⟶ X) (f2 : U2 ⟶ X)
    (i : Fin 2) : finTwo U1 U2 i ⟶ X :=
  match i with
  | 0 => f1
  | 1 => f2

/-- The zero component of `finTwo` is the first space. -/
theorem finTwo_zero (U1 U2 : AlgebraicSpace S) : finTwo U1 U2 0 = U1 :=
  rfl

/-- The zero component of `finTwoHom` is `f1`. -/
theorem finTwoHom_zero {X U1 U2 : AlgebraicSpace S} (f1 : U1 ⟶ X) (f2 : U2 ⟶ X) :
    finTwoHom f1 f2 0 = f1 :=
  rfl

/-- The binary coproduct of algebraic spaces as `coproduct` of a `Fin 2` family. -/
noncomputable abbrev binaryCoproduct (U1 U2 : AlgebraicSpace S) : AlgebraicSpace S :=
  coproduct (finTwo U1 U2)

/-- The binary coproduct is `coproduct` of `finTwo U1 U2`. -/
theorem binaryCoproduct_eq (U1 U2 : AlgebraicSpace S) :
    binaryCoproduct U1 U2 = coproduct (finTwo U1 U2) :=
  rfl

/-- The structure morphism `U1 ⨿ U2 ⟶ X` induced by a pair of morphisms into `X`. -/
noncomputable def coproductStructure {X U1 U2 : AlgebraicSpace S}
    (f1 : U1 ⟶ X) (f2 : U2 ⟶ X) :
    binaryCoproduct U1 U2 ⟶ X :=
  coproductDesc (finTwoHom f1 f2)

/-- The structure morphism of a binary coproduct is `coproductDesc` of `finTwoHom`. -/
theorem coproductStructure_eq {X U1 U2 : AlgebraicSpace S} (f1 : U1 ⟶ X) (f2 : U2 ⟶ X) :
    coproductStructure f1 f2 = coproductDesc (finTwoHom f1 f2) :=
  rfl

/-- The coproduct of two étale morphisms of algebraic spaces is étale. -/
instance etale_coproductDesc {X U1 U2 : AlgebraicSpace S} (f1 : U1 ⟶ X) (f2 : U2 ⟶ X)
    [Etale f1] [Etale f2] : Etale (coproductDesc (finTwoHom f1 f2)) :=
  sorry

/-- Each component of a pair of étale morphisms is étale. -/
instance etale_finTwoHom {X U1 U2 : AlgebraicSpace S} (f1 : U1 ⟶ X) (f2 : U2 ⟶ X)
    (i : Fin 2) [Etale f1] [Etale f2] : Etale (finTwoHom f1 f2 i) :=
  sorry

/-- Coproduct inclusions of algebraic spaces are étale. -/
instance etale_coproductι {I : Type} [Small.{u} I] (F : I → AlgebraicSpace S) (i : I) :
    Etale (coproductι F i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
