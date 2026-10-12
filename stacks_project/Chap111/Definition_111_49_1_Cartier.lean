/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.Ring.Sheaf.Units.Map
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.MeromorphicFunction
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Cartier divisors

A Cartier divisor on a scheme `S` is a global section of the quotient sheaf
`𝒦_S^⁎ / 𝒪_S^⁎`, realized as the cokernel of the additive units map along
`𝒪_S ⟶ 𝒦_S`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})
variable [HasSheafify (Opens.grothendieckTopology S.toTopCat) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology S.toTopCat).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]

/-- The additive sheaf of Cartier divisors is the cokernel of
`𝒪_S^⁎ ⟶ 𝒦_S^⁎`. -/
def cartierDivisorAddSheaf : Sheaf (Opens.grothendieckTopology S.toTopCat) AddCommGrpCat.{u} :=
  cokernel (Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)

/-- The additive Cartier sheaf is the cokernel of the units map from the structure
sheaf to the meromorphic function sheaf. -/
theorem cartierDivisorAddSheaf_eq_cokernel :
    cartierDivisorAddSheaf S =
      cokernel (Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom) :=
  rfl

/-- A Cartier divisor on a scheme is a global section of `𝒦_S^⁎ / 𝒪_S^⁎`. -/
abbrev CartierDivisor : Type u :=
  (cartierDivisorAddSheaf S).1.obj (op ⊤)

/-- Unfold a Cartier divisor as a global section of the additive Cartier sheaf. -/
theorem CartierDivisor_def :
    CartierDivisor S = (cartierDivisorAddSheaf S).1.obj (op ⊤) :=
  rfl

/-- The canonical projection from meromorphic units onto Cartier divisors. -/
def ofMeromorphicUnits
    (f : ((S.toLocallyRingedSpace.meromorphicFunctionSheaf).presheaf.obj (op ⊤))ˣ) :
    CartierDivisor S :=
  ((cokernel.π (Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).hom.app
      (op ⊤)).hom
    (Sheaf.unitsAddSheafSection S.toLocallyRingedSpace.meromorphicFunctionSheaf f)

/-- `ofMeromorphicUnits` is the global component of the cokernel projection on a meromorphic
unit. -/
theorem ofMeromorphicUnits_eq
    (f : ((S.toLocallyRingedSpace.meromorphicFunctionSheaf).presheaf.obj (op ⊤))ˣ) :
    ofMeromorphicUnits S f =
      ((cokernel.π (Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).hom.app
          (op ⊤)).hom
        (Sheaf.unitsAddSheafSection S.toLocallyRingedSpace.meromorphicFunctionSheaf f) :=
  rfl

/-- The structure-sheaf units map into meromorphic units composes to zero with the Cartier
projection. -/
theorem unitsAddMap_toMeromorphic_comp_π :
    Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom ≫
        cokernel.π (Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom) =
      0 :=
  cokernel.condition _

/-- The short complex `𝒪_S^⁎ ⟶ 𝒦_S^⁎ ⟶ 𝒦_S^⁎ / 𝒪_S^⁎`. -/
def cartierDivisorShortComplex :
    ShortComplex (Sheaf (Opens.grothendieckTopology S.toTopCat) AddCommGrpCat.{u}) :=
  ShortComplex.mk
    (Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)
    (cokernel.π (Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom))
    (unitsAddMap_toMeromorphic_comp_π S)

/-- The defining short complex of the Cartier sheaf is the units map followed by its cokernel
projection. -/
theorem cartierDivisorShortComplex_mk :
    cartierDivisorShortComplex S =
      ShortComplex.mk
        (Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)
        (cokernel.π (Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom))
        (unitsAddMap_toMeromorphic_comp_π S) :=
  rfl

/-- The sequence `0 ⟶ 𝒪_S^⁎ ⟶ 𝒦_S^⁎ ⟶ 𝒦_S^⁎ / 𝒪_S^⁎ ⟶ 0` is short exact. -/
theorem cartierDivisorShortComplex_shortExact :
    (cartierDivisorShortComplex S).ShortExact := sorry

scoped notation "CaDiv(" S ")" => CartierDivisor S

end AlgebraicGeometry.Scheme
