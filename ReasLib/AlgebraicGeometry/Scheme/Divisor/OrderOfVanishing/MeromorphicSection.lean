module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.RegularMeromorphicSection
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.OrderOfVanishing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Tactic.CrossRefAttribute

/-!
# Orders of vanishing of meromorphic sections

This file records a local presentation of a meromorphic section at the generic point of a prime
divisor and computes its order of vanishing in the corresponding generic-point stalk.
-/

@[expose] public section

open AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsIntegral X]

/-- Raw fraction data in the generic-point stalk of a prime divisor, together with the dimension
bound required to evaluate its order. -/
structure PrimeDivisorOrderPresentation
    (ℒ : X.Modules) (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (Z : PrimeDivisor X) where
  /-- The generic-point stalk has Krull dimension at most one. -/
  krullDimLE : Ring.KrullDimLE 1 Z.genericPointStalk
  /-- The quotient of the section by a chosen generator at the generic point. -/
  quotient : FractionRing Z.genericPointStalk

/-- Construct raw prime-divisor order data from a fraction in the generic-point stalk. -/
noncomputable def PrimeDivisorOrderPresentation.ofPrimeDivisor
    {ℒ : X.Modules} {s : X.toLocallyRingedSpace.meromorphicSections ℒ}
    (Z : PrimeDivisor X) (quotient : FractionRing Z.genericPointStalk) :
    PrimeDivisorOrderPresentation ℒ s Z where
  krullDimLE := by
    apply krullDimLE_of_coheight_le
    change Order.coheight ((irreducibleSetEquivPoints (α := X)) Z.support) ≤ 1
    rw [Order.coheight_orderIso, Z.coheight_eq_one]
  quotient := quotient

/-- The dimension bound and quotient stored by `ofPrimeDivisor` are the supplied canonical bound
and fraction. -/
theorem PrimeDivisorOrderPresentation.ofPrimeDivisor_spec
    {ℒ : X.Modules} {s : X.toLocallyRingedSpace.meromorphicSections ℒ}
    (Z : PrimeDivisor X) (quotient : FractionRing Z.genericPointStalk) :
    Ring.KrullDimLE 1 Z.genericPointStalk ∧
      (ofPrimeDivisor (ℒ := ℒ) (s := s) Z quotient).quotient = quotient := by
  exact ⟨(ofPrimeDivisor (ℒ := ℒ) (s := s) Z quotient).krullDimLE, rfl⟩

/-- The order attached to a quotient in the fraction field of a prime divisor's generic-point
stalk. -/
def primeDivisorOrderOfVanishingInGenericPointStalk
    (Z : PrimeDivisor X) (quotient : FractionRing Z.genericPointStalk)
    (krullDimLE : Ring.KrullDimLE 1 Z.genericPointStalk) : ℤ :=
  -- Local instance justification (defeq pin): `Ring.ordFrac` must use the
  -- caller-supplied `krullDimLE` dimension bound.
  letI := krullDimLE
  WithZero.log (Ring.ordFrac Z.genericPointStalk quotient)

/-- Unfolding form of `primeDivisorOrderOfVanishingInGenericPointStalk`. -/
theorem primeDivisorOrderOfVanishingInGenericPointStalk_def
    (Z : PrimeDivisor X) (quotient : FractionRing Z.genericPointStalk)
    (krullDimLE : Ring.KrullDimLE 1 Z.genericPointStalk) :
    primeDivisorOrderOfVanishingInGenericPointStalk Z quotient krullDimLE =
      -- Local instance justification (defeq pin): `Ring.ordFrac` must use the
      -- caller-supplied `krullDimLE` dimension bound.
      letI := krullDimLE
      WithZero.log (Ring.ordFrac Z.genericPointStalk quotient) := by
  rfl

/-- The order attached to raw prime-divisor fraction data. -/
def primeDivisorOrderOfVanishing
    {ℒ : X.Modules} (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (Z : PrimeDivisor X) (data : PrimeDivisorOrderPresentation ℒ s Z) : ℤ :=
  primeDivisorOrderOfVanishingInGenericPointStalk Z data.quotient data.krullDimLE

/-- Unfolding form of `primeDivisorOrderOfVanishing`. -/
theorem primeDivisorOrderOfVanishing_def
    {ℒ : X.Modules} {s : X.toLocallyRingedSpace.meromorphicSections ℒ}
    {Z : PrimeDivisor X}
    (data : PrimeDivisorOrderPresentation ℒ s Z) :
    primeDivisorOrderOfVanishing s Z data =
      primeDivisorOrderOfVanishingInGenericPointStalk Z data.quotient data.krullDimLE := by
  rfl

/-- A local presentation computes the order of vanishing through its quotient. -/
theorem PrimeDivisorOrderPresentation.orderOfVanishing_eq
    {ℒ : X.Modules} {s : X.toLocallyRingedSpace.meromorphicSections ℒ}
    {Z : PrimeDivisor X}
    (data : PrimeDivisorOrderPresentation ℒ s Z) :
    primeDivisorOrderOfVanishing s Z data =
      primeDivisorOrderOfVanishingInGenericPointStalk Z data.quotient data.krullDimLE :=
  primeDivisorOrderOfVanishing_def data

/-- An explicit local presentation of a regular meromorphic section along a prime divisor by a
stalk generator and a nonzero fraction. -/
structure RegularMeromorphicSectionOrderPresentation
    (ℒ : X.Modules) [Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s)
    (Z : PrimeDivisor X) where
  /-- An identification of the abstract fraction ring with the meromorphic-function stalk. -/
  fractionRingEquiv :
    FractionRing Z.genericPointStalk ≃ₐ[Z.genericPointStalk]
      (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk Z.genericPoint)
  /-- A chosen generator of the module stalk at the generic point. -/
  generator :
    (SheafOfModules.stalkFunctorOfCommRing X.toLocallyRingedSpace.𝒪 Z.genericPoint).obj ℒ
  /-- The chosen stalk element generates the whole stalk. -/
  generator_span :
    Submodule.span (X.toLocallyRingedSpace.𝒪.presheaf.stalk Z.genericPoint) {generator} = ⊤
  /-- The nonzero fraction expressing the section relative to the chosen generator. -/
  quotient : (FractionRing Z.genericPointStalk)ˣ
  /-- The germ of the section is the quotient times the meromorphic image of the generator. -/
  germ_eq :
    SheafOfModules.sectionGermOfCommRing s Z.genericPoint =
      fractionRingEquiv (quotient : FractionRing Z.genericPointStalk) •
        X.toLocallyRingedSpace.meromorphicSectionStalkMap ℒ Z.genericPoint generator

namespace RegularMeromorphicSectionOrderPresentation

/-- Construct a regular-meromorphic-section order presentation from its explicit generator,
fraction, comparison equivalence, and compatibility laws. -/
noncomputable def ofGenerator
    {ℒ : X.Modules} [Modules.Invertible ℒ]
    {s : X.toLocallyRingedSpace.meromorphicSections ℒ} {Z : PrimeDivisor X}
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s)
    (fractionRingEquiv : FractionRing Z.genericPointStalk ≃ₐ[Z.genericPointStalk]
      (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk Z.genericPoint))
    (generator :
      (SheafOfModules.stalkFunctorOfCommRing X.toLocallyRingedSpace.𝒪 Z.genericPoint).obj ℒ)
    (generator_span :
      Submodule.span (X.toLocallyRingedSpace.𝒪.presheaf.stalk Z.genericPoint) {generator} = ⊤)
    (quotient : (FractionRing Z.genericPointStalk)ˣ)
    (germ_eq : SheafOfModules.sectionGermOfCommRing s Z.genericPoint =
      fractionRingEquiv (quotient : FractionRing Z.genericPointStalk) •
        X.toLocallyRingedSpace.meromorphicSectionStalkMap ℒ Z.genericPoint generator) :
    RegularMeromorphicSectionOrderPresentation ℒ s hs Z where
  fractionRingEquiv := fractionRingEquiv
  generator := generator
  generator_span := generator_span
  quotient := quotient
  germ_eq := germ_eq

/-- A presentation simultaneously records generation of the stalk and the local quotient
equation. -/
theorem spec
    {ℒ : X.Modules} [Modules.Invertible ℒ]
    {s : X.toLocallyRingedSpace.meromorphicSections ℒ} {Z : PrimeDivisor X}
    {hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s}
    (data : RegularMeromorphicSectionOrderPresentation ℒ s hs Z) :
    Submodule.span (X.toLocallyRingedSpace.𝒪.presheaf.stalk Z.genericPoint)
        {data.generator} = ⊤ ∧
      SheafOfModules.sectionGermOfCommRing s Z.genericPoint =
        data.fractionRingEquiv (data.quotient : FractionRing Z.genericPointStalk) •
          X.toLocallyRingedSpace.meromorphicSectionStalkMap ℒ Z.genericPoint
            data.generator := by
  exact ⟨data.generator_span, data.germ_eq⟩

/-- The local quotient transported to the function field of the integral scheme. -/
noncomputable def toFunctionFieldUnit
    {ℒ : X.Modules} [Modules.Invertible ℒ]
    {s : X.toLocallyRingedSpace.meromorphicSections ℒ} {Z : PrimeDivisor X}
    {hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s}
    (data : RegularMeromorphicSectionOrderPresentation ℒ s hs Z) : X.functionFieldˣ :=
  Units.map (FractionRing.algEquiv Z.genericPointStalk X.functionField).toMonoidHom
    data.quotient

/-- The order computed from an explicit generator-and-quotient presentation. -/
noncomputable def order
    {ℒ : X.Modules} [Modules.Invertible ℒ]
    {s : X.toLocallyRingedSpace.meromorphicSections ℒ} {Z : PrimeDivisor X}
    {hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s}
    (data : RegularMeromorphicSectionOrderPresentation ℒ s hs Z) : ℤ :=
  X.ord (data.toFunctionFieldUnit : X.functionField) Z.genericPoint

/-- Every regular meromorphic section admits a generator-and-quotient presentation along a prime
divisor. -/
theorem nonempty
    {ℒ : X.Modules} [Modules.Invertible ℒ]
    {s : X.toLocallyRingedSpace.meromorphicSections ℒ}
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s)
    (Z : PrimeDivisor X) :
    Nonempty (RegularMeromorphicSectionOrderPresentation ℒ s hs Z) := sorry

/-- Any two generator-and-quotient presentations of the same regular meromorphic section have
the same order. -/
theorem order_eq
    {ℒ : X.Modules} [Modules.Invertible ℒ]
    {s : X.toLocallyRingedSpace.meromorphicSections ℒ} {Z : PrimeDivisor X}
    {hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s}
    (data data' : RegularMeromorphicSectionOrderPresentation ℒ s hs Z) :
    data.order = data'.order := sorry

end RegularMeromorphicSectionOrderPresentation

/-- The order of a regular meromorphic section along a prime divisor. -/
noncomputable def regularMeromorphicSectionOrderAlongPrimeDivisor
    {ℒ : X.Modules} [Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s)
    (Z : PrimeDivisor X) : ℤ :=
  sInf (Set.range fun data : RegularMeromorphicSectionOrderPresentation ℒ s hs Z => data.order)

/-- The canonical order of a regular meromorphic section is computed by every explicit local
presentation. -/
theorem regularMeromorphicSectionOrderAlongPrimeDivisor_eq_presentation
    {ℒ : X.Modules} [Modules.Invertible ℒ]
    {s : X.toLocallyRingedSpace.meromorphicSections ℒ} {Z : PrimeDivisor X}
    {hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s}
    (data : RegularMeromorphicSectionOrderPresentation ℒ s hs Z) :
    regularMeromorphicSectionOrderAlongPrimeDivisor s hs Z = data.order := sorry

/-- The order of a regular meromorphic section is the fraction-ring order of its quotient by any
chosen generator at the generic point. -/
theorem regularMeromorphicSectionOrderAlongPrimeDivisor_eq_localOrder
    {ℒ : X.Modules} [Modules.Invertible ℒ]
    {s : X.toLocallyRingedSpace.meromorphicSections ℒ} {Z : PrimeDivisor X}
    {hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s}
    (data : RegularMeromorphicSectionOrderPresentation ℒ s hs Z) :
    regularMeromorphicSectionOrderAlongPrimeDivisor s hs Z =
      -- Local instance justification (defeq pin): `Ring.ordFrac` must use the
      -- dimension bound canonically derived from this prime divisor.
      letI : Ring.KrullDimLE 1 Z.genericPointStalk :=
        (PrimeDivisorOrderPresentation.ofPrimeDivisor (ℒ := ℒ) (s := s) Z
          data.quotient).krullDimLE
      WithZero.log (Ring.ordFrac Z.genericPointStalk
        (data.quotient : FractionRing Z.genericPointStalk)) := sorry

end AlgebraicGeometry.Scheme
