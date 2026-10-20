module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Cartier
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Affine
public import ReasLib.Topology.Sheaves.Glue

/-!
# Cartier divisor associated to an effective Cartier divisor

On an arbitrary scheme, an effective Cartier divisor determines a Cartier divisor
by gluing the local classes of its nonzerodivisor equations in `𝒦_S^⁎ / 𝒪_S^⁎`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}
variable [HasSheafify (Opens.grothendieckTopology S.toTopCat) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology S.toTopCat).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]

/-- The local Cartier class of a meromorphic unit on an open `U`. -/
def ofMeromorphicUnitsOn (U : S.Opens)
    (f : ((S.toLocallyRingedSpace.meromorphicFunctionSheaf).presheaf.obj (op U))ˣ) :
    (cartierDivisorAddSheaf S).1.obj (op U) :=
  ((cokernel.π (Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).hom.app
      (op U)).hom
    (Sheaf.unitsAddSheafSection S.toLocallyRingedSpace.meromorphicFunctionSheaf f)

/-- `ofMeromorphicUnitsOn` is the `U`-component of the cokernel projection on a meromorphic
unit. -/
theorem ofMeromorphicUnitsOn_eq (U : S.Opens)
    (f : ((S.toLocallyRingedSpace.meromorphicFunctionSheaf).presheaf.obj (op U))ˣ) :
    ofMeromorphicUnitsOn U f =
      ((cokernel.π (Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).hom.app
          (op U)).hom
        (Sheaf.unitsAddSheafSection S.toLocallyRingedSpace.meromorphicFunctionSheaf f) :=
  rfl

/-- Global `ofMeromorphicUnits` is the `U = ⊤` case of `ofMeromorphicUnitsOn`. -/
theorem ofMeromorphicUnits_eq_ofMeromorphicUnitsOn_top
    (f : ((S.toLocallyRingedSpace.meromorphicFunctionSheaf).presheaf.obj (op ⊤))ˣ) :
    ofMeromorphicUnits S f = ofMeromorphicUnitsOn (⊤ : S.Opens) f :=
  rfl

/-- A nonzerodivisor on an affine open is a meromorphic-function denominator. -/
theorem mem_meromorphicFunctionDenominators_of_mem_nonZeroDivisors
    (U : S.affineOpens) (f : Γ(S, U)) (hf : f ∈ nonZeroDivisors (Γ(S, U))) :
    f ∈ (S.toLocallyRingedSpace.meromorphicFunctionDenominators).obj (op (U : S.Opens)) :=
  sorry

/-- The meromorphic unit on `U` represented by a meromorphic-function denominator. -/
def meromorphicUnitOfDenominator {U : S.Opens} (f : Γ(S, U))
    (hf : f ∈ (S.toLocallyRingedSpace.meromorphicFunctionDenominators).obj (op U)) :
    ((S.toLocallyRingedSpace.meromorphicFunctionSheaf).presheaf.obj (op U))ˣ :=
  let G := S.toLocallyRingedSpace.meromorphicFunctionDenominators
  Units.map
    ((CategoryTheory.toSheafify (Opens.grothendieckTopology S.toTopCat)
          G.localizationPresheaf).app (op U)).hom.toMonoidHom
    (IsLocalization.map_units (G.localizationPresheaf.obj (op U)) ⟨f, hf⟩).unit

/-- The local Cartier class of a meromorphic-function denominator, viewed as a meromorphic
unit. -/
def ofNonZeroDivisor {U : S.Opens} (f : Γ(S, U))
    (hf : f ∈ (S.toLocallyRingedSpace.meromorphicFunctionDenominators).obj (op U)) :
    (cartierDivisorAddSheaf S).1.obj (op U) :=
  ofMeromorphicUnitsOn U (meromorphicUnitOfDenominator f hf)

/-- `ofNonZeroDivisor` is the local Cartier class of the associated meromorphic unit. -/
theorem ofNonZeroDivisor_eq {U : S.Opens} (f : Γ(S, U))
    (hf : f ∈ (S.toLocallyRingedSpace.meromorphicFunctionDenominators).obj (op U)) :
    ofNonZeroDivisor f hf = ofMeromorphicUnitsOn U (meromorphicUnitOfDenominator f hf) :=
  rfl

/-- Two meromorphic-function denominators generating the same principal ideal determine the
same local Cartier class. -/
theorem ofNonZeroDivisor_eq_of_span_eq {U : S.Opens} (f g : Γ(S, U))
    (hf : f ∈ (S.toLocallyRingedSpace.meromorphicFunctionDenominators).obj (op U))
    (hg : g ∈ (S.toLocallyRingedSpace.meromorphicFunctionDenominators).obj (op U))
    (hspan : Ideal.span ({f} : Set (Γ(S, U))) = Ideal.span ({g} : Set (Γ(S, U)))) :
    ofNonZeroDivisor f hf = ofNonZeroDivisor g hg :=
  sorry

/-- An affine local equation consists of an affine open and a specified nonzerodivisor
that generates the ideal of the divisor there. -/
def effectiveCartierLocalEquation (D : S.IdealSheafData) : Type u :=
  Σ U : S.affineOpens,
    {f : Γ(S, U) //
      f ∈ nonZeroDivisors (Γ(S, U)) ∧ D.ideal U = Ideal.span ({f} : Set (Γ(S, U)))}

/-- The open family formed by the support complement and every affine open equipped with
a nonzerodivisor equation for the divisor. -/
def effectiveCartierCover (D : S.IdealSheafData) :
    Option (effectiveCartierLocalEquation D) → S.Opens :=
  fun i ↦
    match i with
    | none => D.support.compl
    | some e => (e.1 : S.Opens)

/-- The support complement and all affine nonzerodivisor equations of an effective Cartier
divisor cover the scheme. -/
theorem effectiveCartierCover_sup (D : S.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] :
    (⊤ : S.Opens) ≤ iSup (effectiveCartierCover D) :=
  sorry

/-- The local Cartier sections are zero on the support complement and the class of the
specified generator on each indexed affine open. -/
def effectiveCartierLocalSection (D : S.IdealSheafData) :
    ∀ i, (cartierDivisorAddSheaf S).1.obj (op (effectiveCartierCover D i)) :=
  fun i ↦
    match i with
    | none => 0
    | some e =>
      ofNonZeroDivisor e.2.1
        (mem_meromorphicFunctionDenominators_of_mem_nonZeroDivisors e.1 e.2.1 e.2.2.1)

/-- The local Cartier classes on the standard cover of an effective Cartier divisor are
compatible. -/
theorem effectiveCartierLocalSection_compatible (D : S.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] :
    TopCat.Presheaf.IsCompatible (cartierDivisorAddSheaf S).1 (effectiveCartierCover D)
      (effectiveCartierLocalSection D) :=
  sorry

/-- The Cartier divisor associated to an effective Cartier divisor, obtained by gluing the
local classes of its nonzerodivisor equations. -/
def cartierDivisor_ofEffectiveCartier (D : S.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] : CartierDivisor S :=
  TopCat.Sheaf.glueOfCompatibleFamily (cartierDivisorAddSheaf S) (effectiveCartierCover D) ⊤
    (fun _ ↦ homOfLE le_top) (effectiveCartierCover_sup D)
    (effectiveCartierLocalSection D) (effectiveCartierLocalSection_compatible D)

/-- On an affine open where `D` is cut out by a nonzerodivisor `f`, the associated Cartier
divisor restricts to the local class of `f`. -/
theorem cartierDivisor_ofEffectiveCartier_spec (D : S.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] (U : S.affineOpens) (f : Γ(S, U))
    (hf : f ∈ nonZeroDivisors (Γ(S, U)))
    (hgen : D.ideal U = Ideal.span ({f} : Set (Γ(S, U)))) :
    (cartierDivisorAddSheaf S).1.map (homOfLE (le_top : (U : S.Opens) ≤ ⊤)).op
        (cartierDivisor_ofEffectiveCartier D) =
      ofNonZeroDivisor f
        (mem_meromorphicFunctionDenominators_of_mem_nonZeroDivisors U f hf) :=
  sorry

/-- The Cartier divisor associated to an effective Cartier divisor vanishes on the open
complement of its support. -/
theorem cartierDivisor_ofEffectiveCartier_eq_zero_on_complement (D : S.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] :
    (cartierDivisorAddSheaf S).1.map
        (homOfLE (le_top : D.support.compl ≤ ⊤)).op
        (cartierDivisor_ofEffectiveCartier D) =
      0 :=
  sorry

/-- If an effective Cartier divisor is globally generated by a meromorphic-function
denominator, the associated Cartier divisor is the class of that denominator. -/
theorem cartierDivisor_ofEffectiveCartier_of_span_top (D : S.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] (f : Γ(S, ⊤))
    (hf : f ∈ (S.toLocallyRingedSpace.meromorphicFunctionDenominators).obj (op ⊤))
    (hgen : ∀ U : S.affineOpens,
      D.ideal U =
        Ideal.span
          ({S.presheaf.map (homOfLE (le_top : (U : S.Opens) ≤ ⊤)).op f} : Set (Γ(S, U)))) :
    cartierDivisor_ofEffectiveCartier D = ofNonZeroDivisor f hf :=
  sorry

end AlgebraicGeometry.Scheme
