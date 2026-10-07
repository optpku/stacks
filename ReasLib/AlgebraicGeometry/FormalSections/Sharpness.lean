module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.PowerQuotient.Module
public import ReasLib.Algebra.Category.ModuleCat.Topology.Limit
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections.Extension
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.OpenComplement
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension
public import ReasLib.RingTheory.MvPowerSeries.Noetherian
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open SheafOfModules.RingedSite.IdealSheaf
open SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule

noncomputable section

universe u

namespace FormalSectionsSharpness

/-- The coefficient ring `k[x, y]` in the formal-sections example. -/
abbrev CoefficientRing (k : Type u) [CommRing k] := MvPolynomial (Fin 2) k

/-- The ambient ring `k[x, y][[s, t]]`, represented by multivariable power series. -/
abbrev AmbientRing (k : Type u) [CommRing k] := MvPowerSeries (Fin 2) (CoefficientRing k)

/-- The coefficient variable `x` in `k[x, y]`, embedded into the power-series ring. -/
abbrev x₀ (k : Type u) [CommRing k] : AmbientRing k :=
  MvPowerSeries.C (MvPolynomial.X (0 : Fin 2))

/-- The coefficient variable `y` in `k[x, y]`, embedded into the power-series ring. -/
abbrev y₀ (k : Type u) [CommRing k] : AmbientRing k :=
  MvPowerSeries.C (MvPolynomial.X (1 : Fin 2))

/-- The formal power-series variable `s`. -/
abbrev s₀ (k : Type u) [CommRing k] : AmbientRing k := MvPowerSeries.X (0 : Fin 2)

/-- The formal power-series variable `t`. -/
abbrev t₀ (k : Type u) [CommRing k] : AmbientRing k := MvPowerSeries.X (1 : Fin 2)

/-- The relation `xs - yt` defining the quotient ring. -/
abbrev relation (k : Type u) [CommRing k] : AmbientRing k := x₀ k * s₀ k - y₀ k * t₀ k

/-- The quotient ring `A = k[x, y][[s, t]]/(xs - yt)`. -/
abbrev Ring (k : Type u) [CommRing k] : Type u :=
  AmbientRing k ⧸ Ideal.span ({relation k} : Set (AmbientRing k))

/-- The image of `x` in `A`. -/
abbrev x (k : Type u) [CommRing k] : Ring k := Ideal.Quotient.mk _ (x₀ k)

/-- The image of `y` in `A`. -/
abbrev y (k : Type u) [CommRing k] : Ring k := Ideal.Quotient.mk _ (y₀ k)

/-- The image of `s` in `A`. -/
abbrev s (k : Type u) [CommRing k] : Ring k := Ideal.Quotient.mk _ (s₀ k)

/-- The image of `t` in `A`. -/
abbrev t (k : Type u) [CommRing k] : Ring k := Ideal.Quotient.mk _ (t₀ k)

/-- The ideal `I = (s, t)` in `A`. -/
abbrev idealI (k : Type u) [CommRing k] : Ideal (Ring k) := Ideal.span ({s k, t k} : Set (Ring k))

/-- The ideal `𝔞 = (x, y, s, t)` in `A`. -/
abbrev deletedIdeal (k : Type u) [CommRing k] : Ideal (Ring k) :=
  Ideal.span ({x k, y k, s k, t k} : Set (Ring k))

/-- The inclusion `(s, t) ⊆ (x, y, s, t)`. -/
theorem idealI_le_deletedIdeal (k : Type u) [CommRing k] : idealI k ≤ deletedIdeal k := sorry

/-- The punctured affine spectrum `X = Spec(A) - V(𝔞)`. -/
noncomputable def puncturedOpen (k : Type u) [Field k] :
    (Spec (CommRingCat.of (Ring k))).Opens :=
  (Scheme.idealSheafDataOfIdealOnSpec (deletedIdeal k)).openComplement

/-- The punctured-open construction is the complement of the deleted ideal. -/
theorem puncturedOpen_def (k : Type u) [Field k] :
    puncturedOpen k = (Scheme.idealSheafDataOfIdealOnSpec (deletedIdeal k)).openComplement := sorry

/-- The ideal sheaf `I 𝒪_X` on the punctured spectrum. -/
noncomputable abbrev idealSheaf (k : Type u) [Field k] :
    (puncturedOpen k).toScheme.IdealSheafData :=
  (Scheme.idealSheafDataOfIdealOnSpec (idealI k)).comap (puncturedOpen k).ι

/-- The structure sheaf of the punctured spectrum as a module over itself. -/
noncomputable abbrev structureModule (k : Type u) [Field k] :
    (puncturedOpen k).toScheme.Modules := SheafOfModules.unit (puncturedOpen k).toScheme.ringCatSheaf

/-- The inverse system of quotient sheaves `𝒪_X / I ^ n 𝒪_X`. -/
noncomputable abbrev quotientSheafSystem (k : Type u) [Field k] :
    SequentialInverseSystem ((puncturedOpen k).toScheme.Modules) :=
  system.{u, u, u} (idealSheaf k).toSubobject (structureModule k)

/-- The inverse system whose stage `n` is `H⁰(X, 𝒪_X / I ^ n 𝒪_X)`. -/
noncomputable abbrev quotientModuleSystem (k : Type u) [Field k] :
    SequentialInverseSystem (ModuleCat (Ring k)) :=
  quotientSheafSystem k ⋙ Scheme.Hom.globalSectionsFunctor (puncturedOpen k).ι

/-- The inverse-limit module model for the formal sections. -/
noncomputable abbrev sectionsModule (k : Type u) [Field k] : ModuleCat (Ring k) :=
  limit (quotientModuleSystem k)

/-- The limit topology on `M` induced by the quotient-section system. -/
noncomputable abbrev sectionsLimitTopology (k : Type u) [Field k] :
    TopologicalSpace (sectionsModule k) := Functor.limitTopology (quotientModuleSystem k)

/-- The image of `1` in `H⁰(X, 𝒪_X / I ^ n 𝒪_X)`. -/
noncomputable def quotientStageUnit (k : Type u) [Field k] (n : ℕ) :
    (quotientModuleSystem k).obj (op n) :=
  ((Scheme.Hom.globalSectionsFunctor (puncturedOpen k).ι).map
      (projection (idealSheaf k).toSubobject (structureModule k) n)).hom
    (Scheme.Hom.globalSectionsMap (puncturedOpen k).ι 1)

/-- The stage-unit specification exposes the quotient image of the global unit. -/
theorem quotientStageUnit_apply (k : Type u) [Field k] (n : ℕ) :
    quotientStageUnit k n =
      ((Scheme.Hom.globalSectionsFunctor (puncturedOpen k).ι).map
          (projection (idealSheaf k).toSubobject (structureModule k) n)).hom
        (Scheme.Hom.globalSectionsMap (puncturedOpen k).ι 1) := sorry

/-- The section-power sequence represented by the rational function `g = t / x = s / y`. -/
abbrev SectionPower (k : Type u) [Field k] := ℕ → sectionsModule k

/-- The restriction to `V` of an element of `A`, viewed as a regular function on `X`. -/
noncomputable def elementOnNeighborhood (k : Type u) [Field k] (V : (puncturedOpen k).toScheme.Opens)
    (a : Ring k) : Γ((puncturedOpen k).toScheme, V) :=
  (puncturedOpen k).toScheme.presheaf.map V.leTop.op
    (Scheme.Hom.globalSectionsMap (puncturedOpen k).ι a)

/-- Restriction to a neighborhood is the structure-sheaf restriction of the corresponding global function. -/
theorem elementOnNeighborhood_def (k : Type u) [Field k]
    (V : (puncturedOpen k).toScheme.Opens) (a : Ring k) :
    elementOnNeighborhood k V a =
      (puncturedOpen k).toScheme.presheaf.map V.leTop.op
        (Scheme.Hom.globalSectionsMap (puncturedOpen k).ι a) := sorry

-- Local declaration justification (metaprogramming implementation): Lean's module system
-- must expose the private cover body to the public neighborhood and gluing constructions.
set_option backward.privateInPublic true in
/-- The two principal opens on which the rational section has its displayed formulas. -/
private def fractionCover (k : Type u) [Field k] : Bool → (puncturedOpen k).toScheme.Opens
  | true => (puncturedOpen k).toScheme.basicOpen
      (Scheme.Hom.globalSectionsMap (puncturedOpen k).ι (x k))
  | false => (puncturedOpen k).toScheme.basicOpen
      (Scheme.Hom.globalSectionsMap (puncturedOpen k).ι (y k))

-- Local declaration justification (metaprogramming implementation): Lean's exposed public
-- neighborhood needs access to the private principal-open cover.
set_option backward.privateInPublic true in
/-- The neighborhood where `t / x = s / y` is regular. -/
noncomputable def rationalSectionNeighborhood (k : Type u) [Field k] :
    (puncturedOpen k).toScheme.Opens := ⨆ i, fractionCover k i

-- Local declaration justification (metaprogramming implementation): Lean's module system
-- must expose the private fraction family to the public gluing construction.
set_option backward.privateInPublic true in
/-- The local section given by `t / x` on `D(x)` and `s / y` on `D(y)`. -/
private noncomputable def fractionLocalSection (k : Type u) [Field k] :
    ∀ i, Γ((structureModule k), fractionCover k i)
  | true => elementOnNeighborhood k (fractionCover k true) (t k) *
      Ring.inverse (elementOnNeighborhood k (fractionCover k true) (x k))
  | false => elementOnNeighborhood k (fractionCover k false) (s k) *
      Ring.inverse (elementOnNeighborhood k (fractionCover k false) (y k))

-- Local declaration justification (metaprogramming implementation): Lean's module system
-- must expose the private overlap law to the public gluing construction.
set_option backward.privateInPublic true in
/-- The two local fraction formulas agree on the overlap. -/
private theorem fractionLocalSection_compatible (k : Type u) [Field k] :
    TopCat.Presheaf.IsCompatible
      (⟨(structureModule k).presheaf, (structureModule k).isSheaf⟩ :
        TopCat.Sheaf AddCommGrpCat (puncturedOpen k).toScheme).obj
      (fractionCover k) (fractionLocalSection k) := sorry

-- Local declaration justification (metaprogramming implementation): Lean's exposed public
-- gluing needs access to the private cover, local fractions, and overlap law.
set_option backward.privateInPublic true in
/-- The glued regular section `g = t / x = s / y` on the neighborhood. -/
noncomputable def gluedRationalSection (k : Type u) [Field k] :
    Γ((puncturedOpen k).toScheme, rationalSectionNeighborhood k) :=
  TopCat.Sheaf.glueOfCompatibleFamily
    (⟨(structureModule k).presheaf, (structureModule k).isSheaf⟩ :
      TopCat.Sheaf AddCommGrpCat (puncturedOpen k).toScheme)
    (fractionCover k) (rationalSectionNeighborhood k)
    (fun i => homOfLE (le_iSup (fractionCover k) i)) le_rfl
    (fractionLocalSection k)
    (fractionLocalSection_compatible k)

/-- The glued section satisfies the two fraction-presentation equations. -/
theorem gluedRationalSection_spec (k : Type u) [Field k] :
    elementOnNeighborhood k (rationalSectionNeighborhood k) (x k) * gluedRationalSection k =
        elementOnNeighborhood k (rationalSectionNeighborhood k) (t k) ∧
      elementOnNeighborhood k (rationalSectionNeighborhood k) (y k) * gluedRationalSection k =
        elementOnNeighborhood k (rationalSectionNeighborhood k) (s k) := sorry

/-- The two quotient-stage equations for the `e`th power at stage `n`. -/
def powerStageEquation (k : Type u) [Field k] (e n : ℕ)
    (z : (quotientModuleSystem k).obj (op n)) : Prop :=
  x k ^ e • z = t k ^ e • quotientStageUnit k n ∧
    y k ^ e • z = s k ^ e • quotientStageUnit k n

/-- The neighborhood contains the support of `I 𝒪_X`. -/
theorem rationalSectionNeighborhood_containsIdealSupport (k : Type u) [Field k] :
    ((idealSheaf k).support : Set (puncturedOpen k)) ⊆ rationalSectionNeighborhood k := sorry

-- Local declaration justification (metaprogramming implementation): Lean's module system
-- must expose the private covering law to the public quotient-stage construction.
set_option backward.privateInPublic true in
/-- The neighborhood and the complement of the ideal support cover `X`. -/
private theorem rationalSectionNeighborhood_cover (k : Type u) [Field k] :
    rationalSectionNeighborhood k ⊔ (idealSheaf k).openComplement = ⊤ := sorry

-- Local declaration justification (metaprogramming implementation): Lean's module system
-- must expose the private vanishing law to the public quotient-stage construction.
set_option backward.privateInPublic true in
/-- Every quotient stage vanishes on an open contained in the ideal-support complement. -/
private theorem quotientSheafSystem_zeroOnComplement (k : Type u) [Field k] (n : ℕ)
    (U : (puncturedOpen k).toScheme.Opens) (hU : U ≤ (idealSheaf k).openComplement) :
    ∀ z : Γ((quotientSheafSystem k).obj (op n), U), z = 0 := sorry

-- Local declaration justification (metaprogramming implementation): Lean's exposed public
-- stage construction needs access to the private covering and vanishing laws.
set_option backward.privateInPublic true in
/-- The image of `g ^ e` at stage `n`, extended by zero from the rational-section neighborhood. -/
noncomputable def rationalSectionPowerStage (k : Type u) [Field k] (e n : ℕ) :
    (quotientModuleSystem k).obj (op n) :=
  AlgebraicGeometry.Scheme.Modules.extendOfZeroOn
    ((quotientSheafSystem k).obj (op n)) (rationalSectionNeighborhood k)
    (idealSheaf k).openComplement (rationalSectionNeighborhood_cover k)
    (quotientSheafSystem_zeroOnComplement k n)
    (Scheme.Modules.Hom.app (projection (idealSheaf k).toSubobject (structureModule k) n)
      (rationalSectionNeighborhood k) (gluedRationalSection k ^ e))

/-- The stage section restricts to the quotient image of the actual power `g ^ e`. -/
theorem rationalSectionPowerStage_restrict (k : Type u) [Field k] (e n : ℕ) :
    ((quotientSheafSystem k).obj (op n)).presheaf.map
        (rationalSectionNeighborhood k).leTop.op (rationalSectionPowerStage k e n) =
      Scheme.Modules.Hom.app (projection (idealSheaf k).toSubobject (structureModule k) n)
        (rationalSectionNeighborhood k) (gluedRationalSection k ^ e) := sorry

-- Local declaration justification (metaprogramming implementation): Lean's module system
-- must expose the private compatibility law to the public inverse-limit construction.
set_option backward.privateInPublic true in
/-- The explicit stage family is compatible with every morphism in the quotient system. -/
private theorem rationalSectionPowerStage_compatible (k : Type u) [Field k] (e : ℕ) :
    ∀ {n m : ℕᵒᵖ} (f : n ⟶ m),
      ((quotientModuleSystem k ⋙ forget (ModuleCat (Ring k))).map f)
          (rationalSectionPowerStage k e n.unop) =
        rationalSectionPowerStage k e m.unop := sorry

-- Local declaration justification (metaprogramming implementation): Lean's exposed public
-- limit construction needs access to the private stage-compatibility law.
set_option backward.privateInPublic true in
/-- The compatible stage family determines the corresponding inverse-limit element. -/
noncomputable def rationalSectionPowerValues (k : Type u) [Field k] : SectionPower k := fun e =>
  (CategoryTheory.Limits.Types.isLimitEquivSections
    (isLimitOfPreserves (forget (ModuleCat (Ring k)))
        (limit.isLimit (quotientModuleSystem k)))).symm
    ⟨fun n => rationalSectionPowerStage k e n.unop,
      rationalSectionPowerStage_compatible k e⟩

/-- Every limit projection is the explicitly constructed stage section. -/
theorem rationalSectionPowerValues_apply (k : Type u) [Field k] (e n : ℕ) :
    (limit.π (quotientModuleSystem k) (op n)).hom (rationalSectionPowerValues k e) =
      rationalSectionPowerStage k e n := sorry

/-- The explicitly constructed powers satisfy the displayed stage equations. -/
theorem rationalSectionPowerValues_spec (k : Type u) [Field k] (e n : ℕ) :
    powerStageEquation k e n
      ((limit.π (quotientModuleSystem k) (op n)).hom (rationalSectionPowerValues k e)) := sorry

/-- The ideal-submodule `I M` inside the inverse-limit module. -/
abbrev idealMultiple (k : Type u) [Field k] : Submodule (Ring k) (sectionsModule k) :=
  idealI k • (⊤ : Submodule (Ring k) (sectionsModule k))

/-- A sequence maps to zero at its own quotient stage. -/
def VanishesAtOwnStage (k : Type u) [Field k] (gPower : SectionPower k) : Prop :=
  ∀ e : ℕ, (limit.π (quotientModuleSystem k) (op e)).hom (gPower e) = 0

/-- A section-power sequence converges to zero in the inverse-limit topology. -/
def ConvergesToZero (k : Type u) [Field k] (gPower : SectionPower k) : Prop :=
  Filter.Tendsto gPower Filter.atTop (Functor.limitNhds (quotientModuleSystem k) 0)

/-- The powers of the rational section stay outside `I M`. -/
def AvoidsIdealMultiple (k : Type u) [Field k] (gPower : SectionPower k) : Prop :=
  ∀ e : ℕ, gPower e ∉ idealMultiple k

/-- The powers of the fixed rational section vanish at their own stages and converge to zero. -/
theorem rationalSectionPowersConverges (k : Type u) [Field k] :
    VanishesAtOwnStage k (rationalSectionPowerValues k) ∧
      ConvergesToZero k (rationalSectionPowerValues k) := sorry

/-- The same powers are not contained in `I M` at any exponent. -/
theorem rationalSectionPowersAvoidIdeal (k : Type u) [Field k] :
    AvoidsIdealMultiple k (rationalSectionPowerValues k) := sorry

/-- The ideal `I` in the quotient ring has local-cohomological dimension `2`. -/
theorem localCohomologyDimension_eq_two (k : Type u) [Field k] :
    Ideal.LocalCohomology.dimension (idealI k) (idealI k).fg_of_isNoetherianRing = 2 := sorry

end FormalSectionsSharpness
