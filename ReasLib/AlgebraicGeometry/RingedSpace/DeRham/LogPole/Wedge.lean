/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.LogPole.ResidueSequence
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.GaussManin.DifferentialGraded
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.DegreeOne
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Multiplication
public import ReasLib.Algebra.Homology.Embedding.UpNatMonoidal

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.DeRham.LogPole.Canonical

/-- The local logarithmic generator, regarded before restriction of scalars as a section of
`Ω^p_[X/S] ⊗ 𝒪_X(Y)`. -/
noncomputable def formGeneratorSection {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] : ∀ (p : ℕ) (g : Generator f i p),
      (tensorObj (RingedSpace.DeRham.form f.toLRSHom.toShHom p)
        (poleLine i)).val.obj (Opposite.op (generatorOpen f i p g))
  | 0, g =>
      ((((ρ_ (RingedSpace.DeRham.form f.toLRSHom.toShHom 0)).inv ≫
        tensorHom (𝟙 _) (poleUnitSectionHom i))).val.app (Opposite.op g.1)).hom g.2
  | p + 1, Sum.inl g =>
      ((((ρ_ (RingedSpace.DeRham.form f.toLRSHom.toShHom (p + 1))).inv ≫
        tensorHom (𝟙 _) (poleUnitSectionHom i))).val.app (Opposite.op g.1)).hom g.2
  | p + 1, Sum.inr g =>
      SheafOfModules.RingedSite.tensorSection X.sheaf (Opposite.op g.1)
        (dlogNumeratorSection f i p g) g.2.2.1

/-- The generated subobject of simple-pole forms containing the ordinary and `dlog`
generators. -/
noncomputable def formSubobject {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) :
    Subobject (tensorObj (RingedSpace.DeRham.form f.toLRSHom.toShHom p) (poleLine i)) :=
  SheafOfModules.Subobject.generatedBySections _ (generatorOpen f i p)
    (formGeneratorSection f i p)

/-- The `𝒪_X`-module sheaf `Ω^p_[X/S](log Y)`. -/
noncomputable abbrev form {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) : X.Modules :=
  Subobject.underlying.obj (formSubobject f i p)

/-- The inclusion of logarithmic forms into forms with a simple pole. -/
noncomputable def formInclusion {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) :
    form f i p ⟶ tensorObj (RingedSpace.DeRham.form f.toLRSHom.toShHom p) (poleLine i) :=
  (formSubobject f i p).arrow

/-- The ordinary relative `p`-forms map to simple-pole forms by multiplication with the
canonical section of `𝒪_X(Y)`. -/
noncomputable def ordinaryFormToPole {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) :
    RingedSpace.DeRham.form f.toLRSHom.toShHom p ⟶
      tensorObj (RingedSpace.DeRham.form f.toLRSHom.toShHom p) (poleLine i) :=
  (ρ_ (RingedSpace.DeRham.form f.toLRSHom.toShHom p)).inv ≫
    tensorHom (𝟙 _) (poleUnitSectionHom i)

/-- The ordinary-form map factors through the generated logarithmic-form subobject. -/
theorem ordinaryFormToPole_factors {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) :
    (formSubobject f i p).Factors (ordinaryFormToPole f i p) := sorry

/-- The `𝒪_X`-linear inclusion of ordinary forms into logarithmic forms. -/
noncomputable def ordinaryFormInclusion {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) :
    RingedSpace.DeRham.form f.toLRSHom.toShHom p ⟶ form f i p :=
  (formSubobject f i p).factorThru (ordinaryFormToPole f i p)
    (ordinaryFormToPole_factors f i p)

/-- A pair of mutually inverse scalar-restriction maps between the `𝒪_X`-linear and
`f⁻¹𝒪_S`-linear logarithmic terms. -/
abbrev FormRestrictionPair {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) :=
  (((SheafOfModules.RingedSite.restrictionAlong
      (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom)).obj (form f i p) ⟶
        (term f i p : Modules f.toLRSHom.toShHom)) ×
    ((term f i p : Modules f.toLRSHom.toShHom) ⟶
      (SheafOfModules.RingedSite.restrictionAlong
        (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom)).obj (form f i p)))

/-- The restriction pair is inverse in both directions and is compatible with the inclusions
into the simple-pole sheaf. -/
def IsFormRestrictionPair {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) (e : FormRestrictionPair f i p) : Prop :=
  e.1 ≫ e.2 = 𝟙 _ ∧ e.2 ≫ e.1 = 𝟙 _ ∧
    e.1 ≫ (term f i p).arrow =
      (SheafOfModules.RingedSite.restrictionAlong
        (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom)).map (formInclusion f i p)

/-- Restriction of scalars identifies the generated `𝒪_X`-linear logarithmic forms with the
canonical logarithmic term. -/
theorem exists_formRestrictionPair {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) :
    ∃ e : FormRestrictionPair f i p, IsFormRestrictionPair f i p e := sorry

/-- The canonical pair of restriction comparison maps, selected by its complete specification. -/
noncomputable def formRestrictionPair {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) : FormRestrictionPair f i p :=
  Classical.epsilon (fun e : FormRestrictionPair f i p ↦ IsFormRestrictionPair f i p e)

/-- The selected restriction comparison pair satisfies its inverse and inclusion laws. -/
theorem formRestrictionPair_spec {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) :
    IsFormRestrictionPair f i p (formRestrictionPair f i p) := sorry

/-- The selected restriction comparison maps compose to the identity on restricted forms. -/
theorem formRestrictionPair_hom_inv {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) :
    (formRestrictionPair f i p).1 ≫ (formRestrictionPair f i p).2 = 𝟙 _ := sorry

/-- The selected restriction comparison maps compose to the identity on canonical terms. -/
theorem formRestrictionPair_inv_hom {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) :
    (formRestrictionPair f i p).2 ≫ (formRestrictionPair f i p).1 = 𝟙 _ := sorry

/-- Restriction of scalars identifies the `𝒪_X`-module logarithmic forms with the terms of the
canonical logarithmic complex. -/
noncomputable def formRestrictionIso {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) :
    (SheafOfModules.RingedSite.restrictionAlong
      (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom)).obj (form f i p) ≅
        (term f i p : Modules f.toLRSHom.toShHom) where
  hom := (formRestrictionPair f i p).1
  inv := (formRestrictionPair f i p).2
  hom_inv_id := formRestrictionPair_hom_inv f i p
  inv_hom_id := formRestrictionPair_inv_hom f i p

/-- Families of `𝒪_X`-bilinear homogeneous products on logarithmic forms. -/
abbrev WedgeFamily {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] :=
  ∀ p q : ℕ, tensorObj (form f i p) (form f i q) ⟶ form f i (p + q)

/-- An ordinary local form, viewed as one of the chosen logarithmic generators. -/
def ordinaryGenerator {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] : ∀ p : ℕ, OrdinaryGenerator f p → Generator f i p
  | 0, g => g
  | _ + 1, g => Sum.inl g

/-- The canonical lift of an ordinary local form to the logarithmic term over the same open. -/
noncomputable def ordinaryGeneratorLift {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] : ∀ (p : ℕ) (g : OrdinaryGenerator f p),
      (term f i p : Modules f.toLRSHom.toShHom).val.obj (Opposite.op g.1)
  | 0, g => generatorLift f i 0 g
  | p + 1, g => generatorLift f i (p + 1) (Sum.inl g)

/-- The ordinary generator obtained by wedging two ordinary local forms on the same open. -/
noncomputable def ordinaryWedgeGenerator {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p q : ℕ) (g : OrdinaryGenerator f p)
    (η : (RingedSpace.DeRham.term f.toLRSHom.toShHom q).val.obj (Opposite.op g.1)) :
    OrdinaryGenerator f (p + q) :=
  ⟨g.1,
    ((SheafOfModules.RingedSite.DeRham.formWedge
      (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) p q).val.app
        (Opposite.op g.1)).hom
      (SheafOfModules.RingedSite.tensorSection X.sheaf (Opposite.op g.1) g.2 η)⟩

/-- The `dlog` generator obtained by wedging a `dlog` generator on the left with an
ordinary local form on the same open. -/
noncomputable def dlogWedgeOrdinaryGenerator {S X Y : Scheme.{u}} (f : X ⟶ S)
    (i : Y ⟶ X) [IsEffectiveCartierDivisor i] (p q : ℕ) (g : DlogGenerator f i p)
    (η : (RingedSpace.DeRham.term f.toLRSHom.toShHom q).val.obj (Opposite.op g.1)) :
    DlogGenerator f i (p + q) :=
  ⟨g.1, g.2.1, g.2.2.1, ⟨
    ((SheafOfModules.RingedSite.DeRham.formWedge
      (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) p q).val.app
        (Opposite.op g.1)).hom
      (SheafOfModules.RingedSite.tensorSection X.sheaf (Opposite.op g.1)
        g.2.2.2.val η), g.2.2.2.property⟩⟩

/-- The `dlog` generator obtained by wedging an ordinary local form on the left with a
`dlog` generator on the same open, including the Koszul sign. -/
noncomputable def ordinaryWedgeDlogGenerator {S X Y : Scheme.{u}} (f : X ⟶ S)
    (i : Y ⟶ X) [IsEffectiveCartierDivisor i] (p q : ℕ) (g : DlogGenerator f i q)
    (ω : (RingedSpace.DeRham.term f.toLRSHom.toShHom p).val.obj (Opposite.op g.1)) :
    DlogGenerator f i (p + q) :=
  ⟨g.1, g.2.1, g.2.2.1, ⟨
    ((-1 : ℤ) ^ p) •
      ((SheafOfModules.RingedSite.DeRham.formWedge
        (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) p q).val.app
          (Opposite.op g.1)).hom
        (SheafOfModules.RingedSite.tensorSection X.sheaf (Opposite.op g.1)
          ω g.2.2.2.val), g.2.2.2.property⟩⟩

/-- The regular ratio of a local equation and a reciprocal local equation. -/
noncomputable def equationRatio {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (U : X.Opens)
    (a : (Subobject.underlying.obj
      (RingedSpace.Hom.idealSheafSubobject i.toShHom)).val.obj (Opposite.op U))
    (binv : (poleLine i).val.obj (Opposite.op U)) :
    X.sheaf.val.obj (Opposite.op U) :=
  (((@Scheme.effectiveCartierDivisorEvaluationHom _ inferInstance
      (RingedSpace.Hom.idealSheafSubobject i.toShHom)
      (idealSheafSubobjectTensorRight i)).val.app (Opposite.op U)).hom
        (SheafOfModules.RingedSite.tensorSection X.sheaf (Opposite.op U) a binv))

/-- The ordinary one-form `dlog(b / a)` determined by two reciprocal local equations. -/
noncomputable def dlogRatioSection {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (U : X.Opens)
    (a b : (Subobject.underlying.obj
      (RingedSpace.Hom.idealSheafSubobject i.toShHom)).val.obj (Opposite.op U))
    (ainv binv : (poleLine i).val.obj (Opposite.op U)) :
    (RingedSpace.DeRham.form f.toLRSHom.toShHom 1).val.obj (Opposite.op U) :=
  equationRatio i U a binv •
    SheafOfModules.RingedSite.DeRham.basicForm
      (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) 1 (Opposite.op U) 1
        (fun _ ↦ equationRatio i U b ainv)

/-- The ordinary factor in the product of two `dlog` generators on one open subset. -/
noncomputable def dlogWedgeDlogFormSection {S X Y : Scheme.{u}} (f : X ⟶ S)
    (i : Y ⟶ X) [IsEffectiveCartierDivisor i] (p q : ℕ) (U : X.Opens)
    (a b : (Subobject.underlying.obj
      (RingedSpace.Hom.idealSheafSubobject i.toShHom)).val.obj (Opposite.op U))
    (ainv binv : (poleLine i).val.obj (Opposite.op U))
    (ω : (RingedSpace.DeRham.form f.toLRSHom.toShHom p).val.obj (Opposite.op U))
    (η : (RingedSpace.DeRham.form f.toLRSHom.toShHom q).val.obj (Opposite.op U)) :
    (RingedSpace.DeRham.form f.toLRSHom.toShHom (p + q + 1)).val.obj
      (Opposite.op U) :=
  ((eqToHom (congrArg
    (fun n : ℕ ↦ RingedSpace.DeRham.form f.toLRSHom.toShHom n)
      (Nat.succ_add p q))).val.app (Opposite.op U)).hom
    (((SheafOfModules.RingedSite.DeRham.formWedge
      (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) (p + 1) q).val.app
        (Opposite.op U)).hom
      (SheafOfModules.RingedSite.tensorSection X.sheaf (Opposite.op U)
        (((SheafOfModules.RingedSite.DeRham.formWedge
          (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) p 1).val.app
            (Opposite.op U)).hom
          (SheafOfModules.RingedSite.tensorSection X.sheaf (Opposite.op U) ω
            (dlogRatioSection f i U a b ainv binv))) η))

/-- The `dlog` generator representing the product of two `dlog` generators on one open
subset, using `dlog(b) = dlog(a) + dlog(b / a)`. -/
noncomputable def dlogWedgeDlogGenerator {S X Y : Scheme.{u}} (f : X ⟶ S)
    (i : Y ⟶ X) [IsEffectiveCartierDivisor i] (p q : ℕ) (U : X.Opens)
    (a b : (Subobject.underlying.obj
      (RingedSpace.Hom.idealSheafSubobject i.toShHom)).val.obj (Opposite.op U))
    (ainv binv : (poleLine i).val.obj (Opposite.op U))
    (ω : Subtype fun _ : (RingedSpace.DeRham.form f.toLRSHom.toShHom p).val.obj
      (Opposite.op U) ↦ IsReciprocal i U a ainv)
    (η : Subtype fun _ : (RingedSpace.DeRham.form f.toLRSHom.toShHom q).val.obj
      (Opposite.op U) ↦ IsReciprocal i U b binv) :
    DlogGenerator f i (p + q + 1) :=
  ⟨U, a, ainv, ⟨dlogWedgeDlogFormSection f i p q U a b ainv binv ω.val η.val,
    ω.property⟩⟩

/-- Transport an `𝒪_X`-bilinear logarithmic product to the canonical `f⁻¹𝒪_S`-linear terms. -/
noncomputable def restrictedWedgeComponent {S X Y : Scheme.{u}} (f : X ⟶ S)
    (i : Y ⟶ X) [IsEffectiveCartierDivisor i] (μ : WedgeFamily f i) (p q : ℕ) :
    tensorObj (term f i p : Modules f.toLRSHom.toShHom) (term f i q) ⟶
      (term f i (p + q) : Modules f.toLRSHom.toShHom) :=
  tensorHom (formRestrictionIso f i p).inv (formRestrictionIso f i q).inv ≫
    SheafOfModules.RingedSite.Restriction.tensorComparison
      (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) (form f i p) (form f i q) ≫
    (SheafOfModules.RingedSite.restrictionAlong
      (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom)).map (μ p q) ≫
    (formRestrictionIso f i (p + q)).hom

/-- A logarithmic product family has the source formulas on ordinary and `dlog` generators. -/
def HasWedgeGeneratorEquations {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (μ : WedgeFamily f i) : Prop :=
  (∀ (p q : ℕ) (g : OrdinaryGenerator f p)
      (η : (RingedSpace.DeRham.term f.toLRSHom.toShHom q).val.obj (Opposite.op g.1)),
    ((restrictedWedgeComponent f i μ p q).val.app (Opposite.op g.1)).hom
        (SheafOfModules.RingedSite.tensorSection
          (RingedSpace.DeRham.coefficients f.toLRSHom.toShHom) (Opposite.op g.1)
          (ordinaryGeneratorLift f i p g)
          (ordinaryGeneratorLift f i q ⟨g.1, η⟩)) =
      ordinaryGeneratorLift f i (p + q) (ordinaryWedgeGenerator f i p q g η)) ∧
  ((∀ (p q : ℕ) (g : DlogGenerator f i p)
      (η : (RingedSpace.DeRham.term f.toLRSHom.toShHom q).val.obj (Opposite.op g.1)),
    HEq (((restrictedWedgeComponent f i μ (p + 1) q).val.app
        (Opposite.op g.1)).hom
          (SheafOfModules.RingedSite.tensorSection
            (RingedSpace.DeRham.coefficients f.toLRSHom.toShHom) (Opposite.op g.1)
            (generatorLift f i (p + 1) (Sum.inr g))
            (ordinaryGeneratorLift f i q ⟨g.1, η⟩)))
      (generatorLift f i (p + q + 1)
        (Sum.inr (dlogWedgeOrdinaryGenerator f i p q g η)))) ∧
  (∀ (p q : ℕ) (g : DlogGenerator f i q)
      (ω : (RingedSpace.DeRham.term f.toLRSHom.toShHom p).val.obj (Opposite.op g.1)),
    HEq (((restrictedWedgeComponent f i μ p (q + 1)).val.app
        (Opposite.op g.1)).hom
          (SheafOfModules.RingedSite.tensorSection
            (RingedSpace.DeRham.coefficients f.toLRSHom.toShHom) (Opposite.op g.1)
            (ordinaryGeneratorLift f i p ⟨g.1, ω⟩)
            (generatorLift f i (q + 1) (Sum.inr g))))
      (generatorLift f i (p + q + 1)
        (Sum.inr (ordinaryWedgeDlogGenerator f i p q g ω))))) ∧
  (∀ (p q : ℕ) (U : X.Opens)
      (a b : (Subobject.underlying.obj
        (RingedSpace.Hom.idealSheafSubobject i.toShHom)).val.obj (Opposite.op U))
      (ainv binv : (poleLine i).val.obj (Opposite.op U))
      (ω : Subtype fun _ : (RingedSpace.DeRham.form f.toLRSHom.toShHom p).val.obj
        (Opposite.op U) ↦ IsReciprocal i U a ainv)
      (η : Subtype fun _ : (RingedSpace.DeRham.form f.toLRSHom.toShHom q).val.obj
        (Opposite.op U) ↦ IsReciprocal i U b binv),
    HEq (((restrictedWedgeComponent f i μ (p + 1) (q + 1)).val.app
        (Opposite.op U)).hom
          (SheafOfModules.RingedSite.tensorSection
            (RingedSpace.DeRham.coefficients f.toLRSHom.toShHom) (Opposite.op U)
            (generatorLift f i (p + 1) (Sum.inr ⟨U, a, ainv, ω⟩))
            (generatorLift f i (q + 1) (Sum.inr ⟨U, b, binv, η⟩))))
      (generatorLift f i (p + q + 2)
        (Sum.inr (dlogWedgeDlogGenerator f i p q U a b ainv binv ω η))))

/-- A logarithmic product family extends the ordinary exterior product, has the explicit
ordinary and `dlog` generator formulas, and obeys the graded Leibniz rule. -/
def IsWedgeFamily {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (μ : WedgeFamily f i) : Prop :=
  (∀ p q : ℕ,
    tensorHom (ordinaryFormInclusion f i p) (ordinaryFormInclusion f i q) ≫ μ p q =
      SheafOfModules.RingedSite.DeRham.formWedge
        (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) p q ≫
          ordinaryFormInclusion f i (p + q)) ∧
  HasWedgeGeneratorEquations f i μ ∧
  (∀ p q : ℕ,
    restrictedWedgeComponent f i μ p q ≫ differential f i h_defined (p + q) =
      (differential f i h_defined p ▷ (term f i q : Modules f.toLRSHom.toShHom)) ≫
          restrictedWedgeComponent f i μ (p + 1) q ≫
          eqToHom (congrArg (fun n ↦ (term f i n : Modules f.toLRSHom.toShHom))
            (Nat.succ_add p q)) +
        ((-1 : ℤ) ^ p) •
          (((term f i p : Modules f.toLRSHom.toShHom) ◁
              differential f i h_defined q) ≫
            restrictedWedgeComponent f i μ p (q + 1) ≫
            eqToHom (congrArg (fun n ↦ (term f i n : Modules f.toLRSHom.toShHom))
              (Nat.add_succ p q))))

/-- There is a unique `𝒪_X`-bilinear logarithmic wedge family with the ordinary and `dlog`
generator formulas and satisfying the graded Leibniz rule. -/
theorem existsUnique_wedgeFamily {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    ∃! μ : WedgeFamily f i, IsWedgeFamily f i h_defined μ := sorry

/-- The canonical logarithmic wedge family, selected by its source characterization. -/
noncomputable def wedgeFamily {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) : WedgeFamily f i :=
  @Classical.epsilon (WedgeFamily f i) ⟨fun _ _ ↦ 0⟩
    (fun μ : WedgeFamily f i ↦ IsWedgeFamily f i h_defined μ)

/-- The canonical logarithmic wedge satisfies its extension and Leibniz specification. -/
theorem wedgeFamily_spec {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    IsWedgeFamily f i h_defined (wedgeFamily f i h_defined) := sorry

/-- Any logarithmic wedge family with the defining properties is the canonical family. -/
theorem wedgeFamily_unique {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (μ : WedgeFamily f i)
    (hμ : IsWedgeFamily f i h_defined μ) : μ = wedgeFamily f i h_defined := sorry

/-- The canonical homogeneous logarithmic wedge product. -/
noncomputable def wedgeComponent {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (p q : ℕ) :
    tensorObj (term f i p : Modules f.toLRSHom.toShHom) (term f i q) ⟶
      (term f i (p + q) : Modules f.toLRSHom.toShHom) :=
  restrictedWedgeComponent f i (wedgeFamily f i h_defined) p q

/-- The canonical logarithmic wedge obeys the graded Leibniz equation. -/
theorem wedgeComponent_leibniz {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (p q : ℕ) :
    wedgeComponent f i h_defined p q ≫ differential f i h_defined (p + q) =
      (differential f i h_defined p ▷ (term f i q : Modules f.toLRSHom.toShHom)) ≫
          wedgeComponent f i h_defined (p + 1) q ≫
          eqToHom (congrArg (fun n ↦ (term f i n : Modules f.toLRSHom.toShHom))
            (Nat.succ_add p q)) +
        ((-1 : ℤ) ^ p) •
          (((term f i p : Modules f.toLRSHom.toShHom) ◁
              differential f i h_defined q) ≫
            wedgeComponent f i h_defined p (q + 1) ≫
            eqToHom (congrArg (fun n ↦ (term f i n : Modules f.toLRSHom.toShHom))
              (Nat.add_succ p q))) := sorry

/-- The wedge morphism on the nonnegative logarithmic de Rham complex. -/
noncomputable def natWedge {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    HomologicalComplex.tensorObj (natComplex f i h_defined) (natComplex f i h_defined) ⟶
      natComplex f i h_defined where
  f n := HomologicalComplex.mapBifunctorDesc
    (K₁ := natComplex f i h_defined) (K₂ := natComplex f i h_defined)
    (F := curriedTensor (Modules f.toLRSHom.toShHom)) (c := up ℕ)
    fun p q h ↦ wedgeComponent f i h_defined p q ≫
      eqToHom (congrArg (natComplex f i h_defined).X h)
  comm' := sorry

/-- The logarithmic wedge on the integral complex, obtained by extension from nonnegative
degrees. -/
noncomputable def wedge {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    HomologicalComplex.tensorObj (complex f i h_defined) (complex f i h_defined) ⟶
      complex f i h_defined :=
  embeddingUpNat.extendTensorHom (natComplex f i h_defined) (natComplex f i h_defined) ≫
    (embeddingUpNat.extendFunctor _).map (natWedge f i h_defined)

/-- The homogeneous multiplication on the integral logarithmic complex. -/
noncomputable abbrev mul {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (n m : ℤ) :=
  HomologicalComplex.Monoidal.tensorHomComponent (wedge f i h_defined) n m

/-- The unit of the logarithmic algebra is the ordinary de Rham unit followed by the canonical
ordinary inclusion. -/
noncomputable def one {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    𝟙_ (Modules f.toLRSHom.toShHom) ⟶ (complex f i h_defined).X 0 :=
  (AlgebraicGeometry.Scheme.DeRham.gaussManinDeRhamDGA f).one ≫
    (ordinaryInclusion f i h_defined).f 0

/-- Associativity of the homogeneous logarithmic wedge. -/
theorem mul_assoc {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (n m k : ℤ) :
    (α_ ((complex f i h_defined).X n) ((complex f i h_defined).X m)
        ((complex f i h_defined).X k)).hom ≫
        ((complex f i h_defined).X n ◁ mul f i h_defined m k) ≫
        mul f i h_defined n (m + k) =
      (mul f i h_defined n m ▷ (complex f i h_defined).X k) ≫
        mul f i h_defined (n + m) k ≫
        eqToHom (congrArg (complex f i h_defined).X (Int.add_assoc n m k)) := sorry

/-- The logarithmic unit is a left identity. -/
theorem one_mul {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (n : ℤ) :
    (λ_ ((complex f i h_defined).X n)).hom =
      (one f i h_defined ▷ (complex f i h_defined).X n) ≫
        mul f i h_defined 0 n ≫
        eqToHom (congrArg (complex f i h_defined).X (zero_add n)) := sorry

/-- The logarithmic unit is a right identity. -/
theorem mul_one {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (n : ℤ) :
    (ρ_ ((complex f i h_defined).X n)).hom =
      ((complex f i h_defined).X n ◁ one f i h_defined) ≫
        mul f i h_defined n 0 ≫
        eqToHom (congrArg (complex f i h_defined).X (add_zero n)) := sorry

/-- The differential on logarithmic forms obeys the graded Leibniz rule. -/
theorem d_mul {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (n m : ℤ) :
    mul f i h_defined n m ≫
        (complex f i h_defined).d (n + m) (n + m + 1) =
      (((complex f i h_defined).d n (n + 1)) ▷ (complex f i h_defined).X m) ≫
          mul f i h_defined (n + 1) m ≫
          eqToHom (congrArg (complex f i h_defined).X
            ((Int.add_assoc n 1 m).trans
              ((congrArg (fun a : ℤ ↦ n + a) (Int.add_comm 1 m)).trans
                (Int.add_assoc n m 1).symm))) +
        n.negOnePow •
          (((complex f i h_defined).X n ◁
              (complex f i h_defined).d m (m + 1)) ≫
            mul f i h_defined n (m + 1) ≫
            eqToHom (congrArg (complex f i h_defined).X
              (Int.add_assoc n m 1).symm)) := sorry

/-- The canonical differential graded algebra of logarithmic relative forms. -/
noncomputable def dga {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    @SheafOfModules.RingedSite.DifferentialGradedAlgebra.{u, u, u}
      _ _ (_root_.Opens.grothendieckTopology X) _ _ _
      (RingedSpace.DeRham.coefficients f.toLRSHom.toShHom) where
  toComplex := complex f i h_defined
  mul := mul f i h_defined
  one := one f i h_defined
  mul_assoc := mul_assoc f i h_defined
  one_mul := one_mul f i h_defined
  mul_one := mul_one f i h_defined
  d_mul := d_mul f i h_defined

/-- The logarithmic DGA has the canonical logarithmic complex as its underlying complex. -/
theorem dga_toComplex {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    (dga f i h_defined).toComplex = complex f i h_defined := sorry

/-- The multiplication of the logarithmic DGA is the homogeneous component of `wedge`. -/
theorem dga_mul {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (n m : ℤ) :
    (dga f i h_defined).mul n m = mul f i h_defined n m := sorry

/-- The ordinary de Rham inclusion preserves the unit of the logarithmic algebra. -/
theorem ordinaryHom_comm_one {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    (AlgebraicGeometry.Scheme.DeRham.gaussManinDeRhamDGA f).one ≫
        (ordinaryInclusion f i h_defined).f 0 = (dga f i h_defined).one := sorry

/-- The ordinary de Rham inclusion preserves homogeneous wedge products. -/
theorem ordinaryHom_comm_mul {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (n m : ℤ) :
    (AlgebraicGeometry.Scheme.DeRham.gaussManinDeRhamDGA f).mul n m ≫
        (ordinaryInclusion f i h_defined).f (n + m) =
      ((ordinaryInclusion f i h_defined).f n ▷
          (AlgebraicGeometry.Scheme.DeRham.gaussManinDeRhamDGA f).toComplex.X m) ≫
        ((dga f i h_defined).toComplex.X n ◁
          (ordinaryInclusion f i h_defined).f m) ≫
        (dga f i h_defined).mul n m := sorry

/-- The canonical inclusion from ordinary to logarithmic forms as a morphism of differential
graded algebras. -/
noncomputable def ordinaryHom {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    @SheafOfModules.RingedSite.DifferentialGradedAlgebra.Hom.{u, u, u}
      _ _ (_root_.Opens.grothendieckTopology X) _ _ _
      (RingedSpace.DeRham.coefficients f.toLRSHom.toShHom)
      (AlgebraicGeometry.Scheme.DeRham.gaussManinDeRhamDGA f) (dga f i h_defined) where
  hom := ordinaryInclusion f i h_defined
  comm_one := ordinaryHom_comm_one f i h_defined
  comm_mul := ordinaryHom_comm_mul f i h_defined

/-- The underlying cochain map of the ordinary DGA homomorphism is the canonical ordinary
inclusion. -/
theorem ordinaryHom_hom {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    (ordinaryHom f i h_defined).hom = ordinaryInclusion f i h_defined := sorry

/-- A candidate pair of inverse maps between the exterior-power sheaf and logarithmic forms. -/
abbrev ExteriorPowerPair {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) :=
  ((ExteriorPower.sheaf X.sheaf (form f i 1) p ⟶ form f i p) ×
    (form f i p ⟶ ExteriorPower.sheaf X.sheaf (form f i 1) p))

/-- Families of comparison pairs between exterior powers and logarithmic forms in every
degree. -/
abbrev ExteriorPowerFamily {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] :=
  ∀ p : ℕ, ExteriorPowerPair f i p

/-- An exterior-power comparison family is inverse in every degree, is the canonical map in
degree one, and transports exterior multiplication to logarithmic wedge. -/
def IsExteriorPowerFamily {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i)
    (e : ExteriorPowerFamily f i) : Prop :=
  (∀ p : ℕ, (e p).1 ≫ (e p).2 = 𝟙 _ ∧ (e p).2 ≫ (e p).1 = 𝟙 _) ∧
  (ExteriorPower.degreeOne X.sheaf (form f i 1) ≫ (e 1).1 = 𝟙 _) ∧
    ∀ p q : ℕ,
      tensorHom (e p).1 (e q).1 ≫ wedgeFamily f i h_defined p q =
        ExteriorPower.mul X.sheaf (form f i 1) p q ≫ (e (p + q)).1

/-- There is a unique normalized multiplicative exterior-power comparison family. -/
theorem existsUnique_exteriorPowerFamily {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    ∃! e : ExteriorPowerFamily f i, IsExteriorPowerFamily f i h_defined e := sorry

/-- The canonical family of exterior-power comparison pairs. -/
noncomputable def exteriorPowerFamily {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    ExteriorPowerFamily f i :=
  Classical.epsilon
    (fun e : ExteriorPowerFamily f i ↦ IsExteriorPowerFamily f i h_defined e)

/-- The canonical exterior-power family satisfies its inverse and multiplication laws. -/
theorem exteriorPowerFamily_spec {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    IsExteriorPowerFamily f i h_defined (exteriorPowerFamily f i h_defined) := sorry

/-- Any normalized multiplicative exterior-power comparison is the canonical family. -/
theorem exteriorPowerFamily_unique {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i)
    (e : ExteriorPowerFamily f i) (he : IsExteriorPowerFamily f i h_defined e) :
    e = exteriorPowerFamily f i h_defined := sorry

/-- The exterior-power comparison maps compose to the identity on the exterior power. -/
theorem exteriorPowerPair_hom_inv {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (p : ℕ) :
    (exteriorPowerFamily f i h_defined p).1 ≫
      (exteriorPowerFamily f i h_defined p).2 = 𝟙 _ := sorry

/-- The exterior-power comparison maps compose to the identity on logarithmic forms. -/
theorem exteriorPowerPair_inv_hom {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (p : ℕ) :
    (exteriorPowerFamily f i h_defined p).2 ≫
      (exteriorPowerFamily f i h_defined p).1 = 𝟙 _ := sorry

/-- The canonical identification `Λ^p Ω^1_[X/S](log Y) ≅ Ω^p_[X/S](log Y)`. -/
noncomputable def exteriorPowerIso {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (p : ℕ) :
    ExteriorPower.sheaf X.sheaf (form f i 1) p ≅ form f i p where
  hom := (exteriorPowerFamily f i h_defined p).1
  inv := (exteriorPowerFamily f i h_defined p).2
  hom_inv_id := exteriorPowerPair_hom_inv f i h_defined p
  inv_hom_id := exteriorPowerPair_inv_hom f i h_defined p

/-- The degree-one component of `exteriorPowerIso` is the canonical first-exterior-power
identification. -/
theorem exteriorPowerIso_hom_degreeOne {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    ExteriorPower.degreeOne X.sheaf (form f i 1) ≫
      (exteriorPowerIso f i h_defined 1).hom = 𝟙 _ := sorry

/-- The homs of `exteriorPowerIso` transport exterior multiplication to logarithmic wedge. -/
theorem exteriorPowerIso_hom_mul {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (p q : ℕ) :
    tensorHom (exteriorPowerIso f i h_defined p).hom
        (exteriorPowerIso f i h_defined q).hom ≫ wedgeFamily f i h_defined p q =
      ExteriorPower.mul X.sheaf (form f i 1) p q ≫
        (exteriorPowerIso f i h_defined (p + q)).hom := sorry

/-- A divisor right action extends restriction of the ordinary wedge product. -/
def IsDivisorRightAction {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    (p q : ℕ)
    (a : tensorObj ((divisorComplex f i).X ((p + 1 : ℕ) : ℤ))
      (RingedSpace.DeRham.term f.toLRSHom.toShHom q) ⟶
        (divisorComplex f i).X ((p + q + 1 : ℕ) : ℤ)) : Prop :=
  tensorHom (divisorRestriction f i p) (𝟙 _) ≫ a =
    SheafOfModules.RingedSite.DeRham.wedgeComponent
        (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) p q ≫
      divisorRestriction f i (p + q) ≫
      eqToHom (congrArg (divisorComplex f i).X
        (congrArg Int.ofNat (Nat.add_assoc p q 1).symm))

/-- The shifted pushed-forward de Rham term on `Y` admits the right action characterized by
restriction of ordinary forms. -/
theorem existsUnique_divisorRightAction {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    (p q : ℕ) :
    ∃! a : tensorObj ((divisorComplex f i).X ((p + 1 : ℕ) : ℤ))
        (RingedSpace.DeRham.term f.toLRSHom.toShHom q) ⟶
          (divisorComplex f i).X ((p + q + 1 : ℕ) : ℤ),
      IsDivisorRightAction f i p q a := sorry

/-- Right multiplication on the shifted divisor complex by a restricted ordinary form. -/
noncomputable def divisorRightActionComponent {S X Y : Scheme.{u}} (f : X ⟶ S)
    (i : Y ⟶ X) (p q : ℕ) :
    tensorObj ((divisorComplex f i).X ((p + 1 : ℕ) : ℤ))
      (RingedSpace.DeRham.term f.toLRSHom.toShHom q) ⟶
        (divisorComplex f i).X ((p + q + 1 : ℕ) : ℤ) :=
  Classical.epsilon (fun a ↦ IsDivisorRightAction f i p q a)

/-- The divisor right action satisfies its restriction-of-wedge characterization. -/
theorem divisorRightActionComponent_spec {S X Y : Scheme.{u}} (f : X ⟶ S)
    (i : Y ⟶ X) (p q : ℕ) :
    IsDivisorRightAction f i p q (divisorRightActionComponent f i p q) := sorry

/-- Degree arithmetic for multiplying a degree-`p + 1` logarithmic form by a degree-`q`
ordinary form before taking residue. -/
theorem wedgeResidueDegree (p q : ℕ) : (p + 1) + q = p + q + 1 := sorry

/-- Residue is compatible with right multiplication by restricted ordinary forms. -/
theorem residue_wedge {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (p q : ℕ) :
    tensorHom (𝟙 (term f i (p + 1) : Modules f.toLRSHom.toShHom))
          (ordinaryInclusionComponent f i q) ≫
        wedgeComponent f i h_defined (p + 1) q ≫
        eqToHom (congrArg (fun n ↦ (term f i n : Modules f.toLRSHom.toShHom))
          (wedgeResidueDegree p q)) ≫
        residueComponent f i h_defined (p + q) =
      tensorHom (residueComponent f i h_defined p)
          (𝟙 (RingedSpace.DeRham.term f.toLRSHom.toShHom q)) ≫
        divisorRightActionComponent f i p q := sorry

end AlgebraicGeometry.RingedSpace.DeRham.LogPole.Canonical
