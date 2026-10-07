module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.Single
public import ReasLib.Algebra.Category.ModuleCat.DualNumber.Epsilon

/-!
# Dual-number cochain columns for the non-additivity of traces

The complexes `A•`, `B•`, `C•` over `k[ε]`, the short-exact-sequence maps, the
vertical endomorphism `1+ε`, and the source homotopy operator `1 : A^1 ⟶ B^0`.
-/

@[expose] public section

open scoped DualNumber
open CategoryTheory CategoryTheory.Limits HomologicalComplex ComplexShape
open ModuleCat.DualNumber

universe u

namespace CochainComplex.DualNumber

noncomputable section

variable (k : Type u) [Field k]

/-- The cochain complex `A•` over `k[ε]`, with the regular module in degree 1. -/
def columnA : CochainComplex (ModuleCat (k[ε])) ℤ :=
  (single (ModuleCat (k[ε])) (up ℤ) 1).obj (ModuleCat.of (k[ε]) (k[ε]))

/-- The canonical identification of `columnA` in degree 1 with the regular dual-number
module. -/
def columnA_X_one : (columnA k).X 1 ≅ ModuleCat.of (k[ε]) (k[ε]) :=
  singleObjXSelf (up ℤ) 1 (ModuleCat.of (k[ε]) (k[ε]))

/-- The complex `columnA` vanishes away from degree 1. -/
theorem isZero_columnA_X_of_ne_one (i : ℤ) (hi : i ≠ 1) :
    IsZero ((columnA k).X i) :=
  sorry

/-- The cochain complex `B•` over `k[ε]`, with multiplication by `ε` in degrees 0 and 1. -/
def columnB : CochainComplex (ModuleCat (k[ε])) ℤ :=
  double (epsEnd (ModuleCat.of (k[ε]) (k[ε]))) (up_mk (0 : ℤ) 1 rfl)

/-- The canonical identification of `columnB` in degree 0 with the regular dual-number
module. -/
def columnB_X_zero : (columnB k).X 0 ≅ ModuleCat.of (k[ε]) (k[ε]) :=
  doubleXIso₀ (epsEnd (ModuleCat.of (k[ε]) (k[ε]))) (up_mk (0 : ℤ) 1 rfl)

/-- The canonical identification of `columnB` in degree 1 with the regular dual-number
module. -/
def columnB_X_one : (columnB k).X 1 ≅ ModuleCat.of (k[ε]) (k[ε]) :=
  doubleXIso₁ (epsEnd (ModuleCat.of (k[ε]) (k[ε]))) (up_mk (0 : ℤ) 1 rfl) zero_ne_one

/-- The differential of `columnB` is multiplication by `ε` after the endpoint
identifications. -/
theorem columnB_d :
    (columnB k).d 0 1 =
      (columnB_X_zero k).hom ≫
        epsEnd (ModuleCat.of (k[ε]) (k[ε])) ≫ (columnB_X_one k).inv :=
  sorry

/-- The cochain complex `C•` over `k[ε]`, with the regular module in degree 0. -/
def columnC : CochainComplex (ModuleCat (k[ε])) ℤ :=
  (single (ModuleCat (k[ε])) (up ℤ) 0).obj (ModuleCat.of (k[ε]) (k[ε]))

/-- The canonical identification of `columnC` in degree 0 with the regular dual-number
module. -/
def columnC_X_zero : (columnC k).X 0 ≅ ModuleCat.of (k[ε]) (k[ε]) :=
  singleObjXSelf (up ℤ) 0 (ModuleCat.of (k[ε]) (k[ε]))

/-- The complex `columnC` vanishes away from degree 0. -/
theorem isZero_columnC_X_of_ne_zero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((columnC k).X i) :=
  sorry

/-- The degree-1 identity into `columnB` vanishes after every outgoing differential. -/
theorem toB_comp_d (i : ℤ) (hi : (up ℤ).Rel 1 i) :
    (columnB_X_one k).inv ≫ (columnB k).d 1 i = 0 :=
  sorry

/-- The source map `A• ⟶ B•`, the identity in degree 1. -/
def toB : columnA k ⟶ columnB k :=
  mkHomFromSingle (columnB_X_one k).inv (toB_comp_d k)

/-- In degree 1, `toB` is the identity after the endpoint identifications. -/
theorem toB_f_one :
    (toB k).f 1 = (columnA_X_one k).hom ≫ (columnB_X_one k).inv :=
  sorry

/-- Incoming differentials of `columnB` vanish after the degree-0 identity to `columnC`. -/
theorem toC_comp_d (i : ℤ) (hi : (up ℤ).Rel i 0) :
    (columnB k).d i 0 ≫ (columnB_X_zero k).hom = 0 :=
  sorry

/-- The source map `B• ⟶ C•`, the identity in degree 0. -/
def toC : columnB k ⟶ columnC k :=
  mkHomToSingle (columnB_X_zero k).hom (toC_comp_d k)

/-- In degree 0, `toC` is the identity after the endpoint identifications. -/
theorem toC_f_zero :
    (toC k).f 0 = (columnB_X_zero k).hom ≫ (columnC_X_zero k).inv :=
  sorry

/-- The vertical endomorphism `1 + ε` of `A•`. -/
def oneAddEps : columnA k ⟶ columnA k :=
  (single (ModuleCat (k[ε])) (up ℤ) 1).map
    (𝟙 (ModuleCat.of (k[ε]) (k[ε])) + epsEnd (ModuleCat.of (k[ε]) (k[ε])))

/-- In degree 1, `oneAddEps` is `1 + ε` after the endpoint identifications. -/
theorem oneAddEps_f_one :
    (oneAddEps k).f 1 =
      (columnA_X_one k).hom ≫
        (𝟙 (ModuleCat.of (k[ε]) (k[ε])) + epsEnd (ModuleCat.of (k[ε]) (k[ε]))) ≫
          (columnA_X_one k).inv :=
  sorry

/-- The homotopy operator with sole nonzero coordinate the identity `A^1 ⟶ B^0`. -/
def leftHomotopyHom (i j : ℤ) : (columnA k).X i ⟶ (columnB k).X j :=
  if h : i = 1 ∧ j = 0 then
    eqToHom (congrArg (fun n ↦ (columnA k).X n) h.1) ≫
      (columnA_X_one k).hom ≫ (columnB_X_zero k).inv ≫
        eqToHom (congrArg (fun n ↦ (columnB k).X n) h.2.symm)
  else 0

/-- The unique nonzero homotopy coordinate is the identity `A^1 ⟶ B^0` after the
endpoint identifications. -/
theorem leftHomotopyHom_one_zero :
    leftHomotopyHom k 1 0 = (columnA_X_one k).hom ≫ (columnB_X_zero k).inv :=
  sorry

/-- The homotopy operator vanishes off adjacent cochain degrees. -/
theorem leftHomotopyHom_zero (i j : ℤ) (hij : ¬ (up ℤ).Rel j i) :
    leftHomotopyHom k i j = 0 :=
  sorry

/-- The homotopy operator satisfies the chain-homotopy equation for
`oneAddEps ≫ toB` and `toB`. -/
theorem leftHomotopyHom_comm (i : ℤ) :
    (oneAddEps k ≫ toB k).f i =
      dNext i (leftHomotopyHom k) + prevD i (leftHomotopyHom k) + (toB k).f i :=
  sorry

/-- The source homotopy witnessing that the left square commutes in `K(k[ε])`. -/
def leftHomotopy : Homotopy (oneAddEps k ≫ toB k) (toB k) :=
  Homotopy.mk (leftHomotopyHom k) (leftHomotopyHom_zero k) (leftHomotopyHom_comm k)

/-- The components of `leftHomotopy` are `leftHomotopyHom`. -/
theorem leftHomotopy_hom (i j : ℤ) :
    (leftHomotopy k).hom i j = leftHomotopyHom k i j :=
  sorry

end

end CochainComplex.DualNumber
