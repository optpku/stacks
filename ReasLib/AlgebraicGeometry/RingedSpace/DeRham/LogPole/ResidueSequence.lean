module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.LogPole
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.Map
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.Wedge
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.GeneratedSubobject
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.AssociatedSheaf
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Subobject.Limits

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.MonoidalClosed ComplexShape
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.DeRham.LogPole

/-- The ordinary relative de Rham complex, extended from nonnegative to integral degrees. -/
noncomputable abbrev ordinaryComplex {S X : Scheme.{u}} (f : X ⟶ S) :
    CochainComplex (Modules f.toLRSHom.toShHom) ℤ :=
  (RingedSpace.DeRham.complex f.toLRSHom.toShHom).extend embeddingUpNat

/-- The integral-degree ordinary complex is the extension of the usual relative de Rham
complex. -/
theorem ordinaryComplex_def {S X : Scheme.{u}} (f : X ⟶ S) :
    ordinaryComplex f =
      (RingedSpace.DeRham.complex f.toLRSHom.toShHom).extend embeddingUpNat := sorry

/-- The commutative square of structure morphisms determined by `Y ⟶ X ⟶ S`. -/
theorem divisorSquare {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X) :
    CommSq i.toLRSHom.toShHom (i ≫ f).toLRSHom.toShHom
      f.toLRSHom.toShHom (𝟙 _) := sorry

/-- The pushed-forward relative de Rham complex of `Y` over `S`, shifted by `-1`. -/
noncomputable def divisorComplex {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X) :
    CochainComplex (Modules f.toLRSHom.toShHom) ℤ :=
  (((RingedSpace.DeRham.pushforwardComplex (divisorSquare f i)).obj
      (RingedSpace.DeRham.complex (i ≫ f).toLRSHom.toShHom)).extend
        embeddingUpNat)⟦(-1 : ℤ)⟧

/-- The divisor complex is the shifted pushforward of the relative de Rham complex of `Y`. -/
theorem divisorComplex_def {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X) :
    divisorComplex f i =
      (((RingedSpace.DeRham.pushforwardComplex (divisorSquare f i)).obj
        (RingedSpace.DeRham.complex (i ≫ f).toLRSHom.toShHom)).extend
          embeddingUpNat)⟦(-1 : ℤ)⟧ := sorry

/-- The line bundle `𝒪_X(Y)`, realized as the internal-Hom dual of the ideal sheaf of `Y`. -/
noncomputable abbrev poleLine {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] : X.Modules :=
  (ihom (RingedSpace.Hom.idealSheaf i.toShHom)).obj
    (SheafOfModules.unit X.ringCatSheaf)

/-- The simple-pole line is the internal-Hom dual of the divisor ideal sheaf. -/
theorem poleLine_def {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] :
    poleLine i =
      (ihom (RingedSpace.Hom.idealSheaf i.toShHom)).obj
        (SheafOfModules.unit X.ringCatSheaf) := sorry

/-- Relative `p`-forms with at most a simple pole along `Y`, namely
`Ω^p_[X/S] ⊗ 𝒪_X(Y)`, with scalars restricted along `f⁻¹𝒪_S ⟶ 𝒪_X`. -/
noncomputable abbrev poleForm {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) :
    Modules f.toLRSHom.toShHom :=
  (SheafOfModules.RingedSite.restrictionAlong
      (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom)).obj
    (tensorObj (RingedSpace.DeRham.form f.toLRSHom.toShHom p) (poleLine i))

/-- A simple-pole relative form is an ordinary relative form tensored with `𝒪_X(Y)`, then
viewed over the relative coefficient sheaf. -/
theorem poleForm_def {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) :
    poleForm f i p =
      (SheafOfModules.RingedSite.restrictionAlong
        (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom)).obj
          (tensorObj (RingedSpace.DeRham.form f.toLRSHom.toShHom p) (poleLine i)) := sorry

namespace Canonical

/-- The ideal subobject of an effective Cartier divisor supplies the tensor-right equivalence
used by the associated-line-bundle constructions. -/
theorem idealSheafSubobjectTensorRight {X Y : Scheme.{u}} (i : Y ⟶ X)
    [h : IsEffectiveCartierDivisor i] :
    Fact (Functor.IsEquivalence
      (tensorRight (Subobject.underlying.obj
        (RingedSpace.Hom.idealSheafSubobject i.toShHom)))) :=
  ⟨Scheme.Modules.Invertible.tensorRight_isEquivalence h.invertibleIdealSheaf⟩

/-- The tensor-unit morphism corresponding to the canonical section of 𝒪_X(Y). -/
noncomputable def poleUnitSectionHom {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] : 𝟙_ (RingedSpace.Modules X.toRingedSpace) ⟶ poleLine i :=
  MonoidalClosed.curry
    ((ρ_ (RingedSpace.Hom.idealSheaf i.toShHom)).hom ≫
      RingedSpace.Hom.idealSheafι i.toShHom)

/-- The pole-section morphism is obtained by currying the ideal-sheaf inclusion. -/
theorem poleUnitSectionHom_def {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] :
    poleUnitSectionHom i = MonoidalClosed.curry
      ((ρ_ (RingedSpace.Hom.idealSheaf i.toShHom)).hom ≫
        RingedSpace.Hom.idealSheafι i.toShHom) := sorry

/-- The canonical inclusion of ordinary relative forms into forms with a simple pole. -/
noncomputable def ordinaryToPoleForm {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) :
    RingedSpace.DeRham.term f.toLRSHom.toShHom p ⟶ poleForm f i p :=
  (SheafOfModules.RingedSite.restrictionAlong
    (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom)).map
      ((ρ_ (RingedSpace.DeRham.form f.toLRSHom.toShHom p)).inv ≫
        tensorHom (𝟙 _) (poleUnitSectionHom i))

/-- The ordinary-form generator is obtained by tensoring with the canonical section of
𝒪_X(Y). -/
theorem ordinaryToPoleForm_def {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) :
    ordinaryToPoleForm f i p =
      (SheafOfModules.RingedSite.restrictionAlong
        (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom)).map
          ((ρ_ (RingedSpace.DeRham.form f.toLRSHom.toShHom p)).inv ≫
            tensorHom (𝟙 _) (poleUnitSectionHom i)) := sorry

/-- A local section of 𝒪_X(Y) is reciprocal to a local ideal section when their
evaluation is the unit section. -/
def IsReciprocal {X Y : Scheme.{u}} (i : Y ⟶ X) [IsEffectiveCartierDivisor i]
    (U : X.Opens)
    (a : (Subobject.underlying.obj
      (RingedSpace.Hom.idealSheafSubobject i.toShHom)).val.obj (Opposite.op U))
    (ainv : (poleLine i).val.obj (Opposite.op U)) : Prop :=
  (((@Scheme.effectiveCartierDivisorEvaluationHom _ inferInstance
      (RingedSpace.Hom.idealSheafSubobject i.toShHom)
      (idealSheafSubobjectTensorRight i)).val.app (Opposite.op U)).hom
        (SheafOfModules.RingedSite.tensorSection X.sheaf (Opposite.op U) a ainv)) =
    (1 : X.sheaf.val.obj (Opposite.op U))

/-- Reciprocal local equations are characterized by evaluation to one. -/
theorem isReciprocal_iff {X Y : Scheme.{u}} (i : Y ⟶ X) [IsEffectiveCartierDivisor i]
    (U : X.Opens)
    (a : (Subobject.underlying.obj
      (RingedSpace.Hom.idealSheafSubobject i.toShHom)).val.obj (Opposite.op U))
    (ainv : (poleLine i).val.obj (Opposite.op U)) :
    IsReciprocal i U a ainv ↔
      (((@Scheme.effectiveCartierDivisorEvaluationHom _ inferInstance
        (RingedSpace.Hom.idealSheafSubobject i.toShHom)
        (idealSheafSubobjectTensorRight i)).val.app (Opposite.op U)).hom
          (SheafOfModules.RingedSite.tensorSection X.sheaf (Opposite.op U) a ainv)) =
      (1 : X.sheaf.val.obj (Opposite.op U)) := sorry

/-- An ordinary local generator in degree p. -/
abbrev OrdinaryGenerator {S X : Scheme.{u}} (f : X ⟶ S) (p : ℕ) :=
  Σ U : X.Opens,
    (RingedSpace.DeRham.term f.toLRSHom.toShHom p).val.obj (Opposite.op U)

/-- A logarithmic local generator dlog(a) ∧ ω in degree p + 1, including the
reciprocal section that realizes division by the local equation a. -/
abbrev DlogGenerator {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) :=
  Σ U : X.Opens,
    Σ a : (Subobject.underlying.obj
      (RingedSpace.Hom.idealSheafSubobject i.toShHom)).val.obj (Opposite.op U),
      Σ ainv : (poleLine i).val.obj (Opposite.op U),
        {ω : (RingedSpace.DeRham.form f.toLRSHom.toShHom p).val.obj (Opposite.op U) //
          IsReciprocal i U a ainv}

/-- The local generators used for the degree-p logarithmic term. -/
def Generator {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] : ℕ → Type u
  | 0 => OrdinaryGenerator f 0
  | p + 1 => OrdinaryGenerator f (p + 1) ⊕ DlogGenerator f i p

/-- Degree-zero generators are ordinary forms. -/
theorem generator_zero {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] :
    Generator f i 0 = OrdinaryGenerator f 0 := sorry

/-- Positive-degree generators are ordinary forms or logarithmic wedges. -/
theorem generator_succ {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) :
    Generator f i (p + 1) = (OrdinaryGenerator f (p + 1) ⊕ DlogGenerator f i p) := sorry

/-- The open subset supporting a logarithmic-term generator. -/
def generatorOpen {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] : ∀ p : ℕ, Generator f i p → X.Opens
  | 0, g => g.1
  | _ + 1, Sum.inl g => g.1
  | _ + 1, Sum.inr g => g.1

/-- The open-support map has the evident value on degree-zero generators. -/
theorem generatorOpen_zero {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (g : OrdinaryGenerator f 0) :
    generatorOpen f i 0 g = g.1 := sorry

/-- The ideal section underlying a local equation, viewed as a function on its open. -/
noncomputable def localEquation {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (U : X.Opens)
    (a : (Subobject.underlying.obj
      (RingedSpace.Hom.idealSheafSubobject i.toShHom)).val.obj (Opposite.op U)) :
    X.sheaf.val.obj (Opposite.op U) :=
  ((RingedSpace.Hom.idealSheafSubobject i.toShHom).arrow.val.app (Opposite.op U)).hom a

/-- The named local equation is the image of the ideal section under the ideal inclusion. -/
theorem localEquation_def {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (U : X.Opens)
    (a : (Subobject.underlying.obj
      (RingedSpace.Hom.idealSheafSubobject i.toShHom)).val.obj (Opposite.op U)) :
    localEquation i U a =
      ((RingedSpace.Hom.idealSheafSubobject i.toShHom).arrow.val.app (Opposite.op U)).hom a := sorry

/-- Restriction of scalars preserves the underlying local section of a pole-form sheaf. -/
noncomputable def restrictPoleSection {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) (U : X.Opens)
    (s : (tensorObj (RingedSpace.DeRham.form f.toLRSHom.toShHom p)
      (poleLine i)).val.obj (Opposite.op U)) :
    (poleForm f i p).val.obj (Opposite.op U) := s

/-- The underlying section is unchanged by scalar restriction. -/
theorem restrictPoleSection_def {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) (U : X.Opens)
    (s : (tensorObj (RingedSpace.DeRham.form f.toLRSHom.toShHom p)
      (poleLine i)).val.obj (Opposite.op U)) :
    restrictPoleSection f i p U s = s := sorry

/-- The wedge da ∧ ω before normalizing the degree expression 1 + p. -/
noncomputable def rawDlogNumeratorSection {S X Y : Scheme.{u}} (f : X ⟶ S)
    (i : Y ⟶ X) [IsEffectiveCartierDivisor i] (p : ℕ) (g : DlogGenerator f i p) :
    (RingedSpace.DeRham.form f.toLRSHom.toShHom (1 + p)).val.obj (Opposite.op g.1) :=
  ((SheafOfModules.RingedSite.DeRham.formWedge
    (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) 1 p).val.app
      (Opposite.op g.1)).hom
    (SheafOfModules.RingedSite.tensorSection X.sheaf (Opposite.op g.1)
      (SheafOfModules.RingedSite.DeRham.basicForm
        (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) 1
          (Opposite.op g.1) 1 (fun _ ↦ localEquation i g.1 g.2.1))
      g.2.2.2.val)

/-- Before reindexing the degree, the logarithmic numerator is the wedge of `da` with `ω`. -/
theorem rawDlogNumeratorSection_spec {S X Y : Scheme.{u}} (f : X ⟶ S)
    (i : Y ⟶ X) [IsEffectiveCartierDivisor i] (p : ℕ) (g : DlogGenerator f i p) :
    rawDlogNumeratorSection f i p g =
      ((SheafOfModules.RingedSite.DeRham.formWedge
        (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) 1 p).val.app
          (Opposite.op g.1)).hom
        (SheafOfModules.RingedSite.tensorSection X.sheaf (Opposite.op g.1)
          (SheafOfModules.RingedSite.DeRham.basicForm
            (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) 1
              (Opposite.op g.1) 1 (fun _ ↦ localEquation i g.1 g.2.1))
          g.2.2.2.val) := sorry

/-- The numerator da ∧ ω of a logarithmic generator. -/
noncomputable def dlogNumeratorSection {S X Y : Scheme.{u}} (f : X ⟶ S)
    (i : Y ⟶ X) [IsEffectiveCartierDivisor i] (p : ℕ) (g : DlogGenerator f i p) :
    (RingedSpace.DeRham.form f.toLRSHom.toShHom (p + 1)).val.obj (Opposite.op g.1) :=
  ((eqToHom (congrArg
    (fun q : ℕ ↦ RingedSpace.DeRham.form f.toLRSHom.toShHom q)
        (Nat.one_add p))).val.app (Opposite.op g.1)).hom
    (rawDlogNumeratorSection f i p g)

/-- The numerator is the wedge of da with ω. -/
theorem dlogNumeratorSection_spec {S X Y : Scheme.{u}} (f : X ⟶ S)
    (i : Y ⟶ X) [IsEffectiveCartierDivisor i] (p : ℕ) (g : DlogGenerator f i p) :
    dlogNumeratorSection f i p g =
      ((eqToHom (congrArg
        (fun q : ℕ ↦ RingedSpace.DeRham.form f.toLRSHom.toShHom q)
            (Nat.one_add p))).val.app (Opposite.op g.1)).hom
        (rawDlogNumeratorSection f i p g) := sorry

/-- The explicit pole form (da ∧ ω) ⊗ a⁻¹ representing dlog(a) ∧ ω. -/
noncomputable def dlogGeneratorSection {S X Y : Scheme.{u}} (f : X ⟶ S)
    (i : Y ⟶ X) [IsEffectiveCartierDivisor i] (p : ℕ) (g : DlogGenerator f i p) :
    (poleForm f i (p + 1)).val.obj (Opposite.op g.1) :=
  restrictPoleSection f i (p + 1) g.1
    (SheafOfModules.RingedSite.tensorSection X.sheaf (Opposite.op g.1)
      (dlogNumeratorSection f i p g) g.2.2.1)

/-- The logarithmic generator is the concrete section (da ∧ ω) ⊗ a⁻¹. -/
theorem dlogGeneratorSection_def {S X Y : Scheme.{u}} (f : X ⟶ S)
    (i : Y ⟶ X) [IsEffectiveCartierDivisor i] (p : ℕ) (g : DlogGenerator f i p) :
    dlogGeneratorSection f i p g = restrictPoleSection f i (p + 1) g.1
      (SheafOfModules.RingedSite.tensorSection X.sheaf (Opposite.op g.1)
        (dlogNumeratorSection f i p g) g.2.2.1) := sorry

/-- The section of Ω^p_[X/S](Y) represented by a generator index. -/
noncomputable def generatorSection {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] : ∀ (p : ℕ) (g : Generator f i p),
      (poleForm f i p).val.obj (Opposite.op (generatorOpen f i p g))
  | 0, g => ((ordinaryToPoleForm f i 0).val.app (Opposite.op g.1)).hom g.2
  | p + 1, Sum.inl g =>
      ((ordinaryToPoleForm f i (p + 1)).val.app (Opposite.op g.1)).hom g.2
  | _ + 1, Sum.inr g => dlogGeneratorSection f i _ g

/-- The degree-p logarithmic forms are the subobject of Ω^p_[X/S](Y) generated by
ordinary forms and the explicit local sections dlog(a) ∧ ω. -/
noncomputable def term {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) : Subobject (poleForm f i p) :=
  SheafOfModules.Subobject.generatedBySections (poleForm f i p)
    (generatorOpen f i p) (generatorSection f i p)

/-- The canonical logarithmic term is exactly the subobject generated by its local generators. -/
theorem term_spec {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) :
    term f i p = SheafOfModules.Subobject.generatedBySections (poleForm f i p)
      (generatorOpen f i p) (generatorSection f i p) := sorry

/-- Every specified ordinary or logarithmic generator belongs to the canonical term. -/
theorem generatorSection_mem {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) (g : Generator f i p) :
    generatorSection f i p g ∈
      SheafOfModules.Subobject.sections (term f i p)
        (Opposite.op (generatorOpen f i p g)) := sorry

/-- The canonical lift of a generating section to the generated logarithmic subobject. -/
noncomputable def generatorLift {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) (g : Generator f i p) :
    (term f i p : Modules f.toLRSHom.toShHom).val.obj
      (Opposite.op (generatorOpen f i p g)) :=
  Classical.choose ((SheafOfModules.Subobject.mem_sections
    (term f i p) (Opposite.op (generatorOpen f i p g))
      (generatorSection f i p g)).mp (generatorSection_mem f i p g))

/-- The lift of a generator maps to the original pole-form section. -/
theorem generatorLift_arrow {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) (g : Generator f i p) :
    SheafOfModules.Subobject.inclusionApp (term f i p)
        (Opposite.op (generatorOpen f i p g)) (generatorLift f i p g) =
      generatorSection f i p g := sorry

/-- The differential of an ordinary local form. -/
noncomputable def ordinaryDifferentialSection {S X : Scheme.{u}} (f : X ⟶ S)
    (p : ℕ) (g : OrdinaryGenerator f p) :
    (RingedSpace.DeRham.term f.toLRSHom.toShHom (p + 1)).val.obj (Opposite.op g.1) :=
  ((RingedSpace.DeRham.d f.toLRSHom.toShHom p).val.app (Opposite.op g.1)).hom g.2

/-- The ordinary differential section is induced by the relative de Rham differential. -/
theorem ordinaryDifferentialSection_def {S X : Scheme.{u}} (f : X ⟶ S)
    (p : ℕ) (g : OrdinaryGenerator f p) :
    ordinaryDifferentialSection f p g =
      ((RingedSpace.DeRham.d f.toLRSHom.toShHom p).val.app (Opposite.op g.1)).hom g.2 := sorry

/-- The differential sends an ordinary generator to its ordinary differential and sends
dlog(a) ∧ ω to -dlog(a) ∧ dω. -/
noncomputable def generatorDifferential {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] : ∀ (p : ℕ), Generator f i p → Generator f i (p + 1)
  | 0, g => Sum.inl ⟨g.1, ordinaryDifferentialSection f 0 g⟩
  | p + 1, Sum.inl g => Sum.inl ⟨g.1, ordinaryDifferentialSection f (p + 1) g⟩
  | p + 1, Sum.inr g =>
      Sum.inr ⟨g.1, g.2.1, g.2.2.1,
        ⟨-ordinaryDifferentialSection f p ⟨g.1, g.2.2.2.val⟩, g.2.2.2.property⟩⟩

/-- A map between consecutive generated terms is the logarithmic differential when it has
the source formula on every ordinary and logarithmic generator. -/
def IsDifferential {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ)
    (d : (term f i p : Modules f.toLRSHom.toShHom) ⟶ term f i (p + 1)) : Prop :=
  ∀ g : Generator f i p,
    HEq ((d.val.app (Opposite.op (generatorOpen f i p g))).hom (generatorLift f i p g))
      (generatorLift f i (p + 1) (generatorDifferential f i p g))

/-- Definability gives a unique differential on the generated logarithmic terms. -/
theorem existsUnique_differential {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (p : ℕ) :
    ∃! d : (term f i p : Modules f.toLRSHom.toShHom) ⟶ term f i (p + 1),
      IsDifferential f i p d := sorry

/-- The canonical logarithmic differential induced on the generated subobjects. -/
noncomputable def differential {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (p : ℕ) :
    (term f i p : Modules f.toLRSHom.toShHom) ⟶ term f i (p + 1) :=
  Classical.choose (existsUnique_differential f i h_defined p)

/-- The canonical differential has the ordinary and dlog generator formulas. -/
theorem differential_spec {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (p : ℕ) :
    IsDifferential f i p (differential f i h_defined p) := sorry

/-- Any map with the prescribed ordinary and logarithmic generator formulas is the canonical
logarithmic differential. -/
theorem differential_unique {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (p : ℕ)
    (d : (term f i p : Modules f.toLRSHom.toShHom) ⟶ term f i (p + 1))
    (hd : IsDifferential f i p d) : d = differential f i h_defined p := sorry

/-- Consecutive canonical logarithmic differentials compose to zero. -/
theorem differential_sq {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (p : ℕ) :
    differential f i h_defined p ≫ differential f i h_defined (p + 1) = 0 := sorry

/-- The canonical nonnegative logarithmic de Rham complex. -/
noncomputable def natComplex {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    CochainComplex (Modules f.toLRSHom.toShHom) ℕ :=
  CochainComplex.of (fun p ↦ (term f i p : Modules f.toLRSHom.toShHom))
    (differential f i h_defined) (differential_sq f i h_defined)

/-- The canonical logarithmic de Rham complex, extended by zero to integral degrees. -/
noncomputable def complex {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    CochainComplex (Modules f.toLRSHom.toShHom) ℤ :=
  (natComplex f i h_defined).extend embeddingUpNat

/-- The integral logarithmic complex is the extension of its generated-subobject complex. -/
theorem complex_spec {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    complex f i h_defined = (natComplex f i h_defined).extend embeddingUpNat := sorry

/-- The ordinary degree-p map factors through the generated logarithmic term. -/
theorem ordinaryToPoleForm_factors {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) :
    (term f i p).Factors (ordinaryToPoleForm f i p) := sorry

/-- The degreewise ordinary-form inclusion into the generated logarithmic term. -/
noncomputable def ordinaryInclusionComponent {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) :
    RingedSpace.DeRham.term f.toLRSHom.toShHom p ⟶ term f i p :=
  (term f i p).factorThru (ordinaryToPoleForm f i p)
    (ordinaryToPoleForm_factors f i p)

/-- The degreewise inclusion followed by the logarithmic-term inclusion is the canonical
ordinary-to-pole-form map. -/
theorem ordinaryInclusionComponent_arrow {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ) :
    ordinaryInclusionComponent f i p ≫ (term f i p).arrow = ordinaryToPoleForm f i p := sorry

/-- The canonical degreewise inclusion of ordinary forms in logarithmic forms. -/
noncomputable def ordinaryInclusionNat {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    RingedSpace.DeRham.complex f.toLRSHom.toShHom ⟶ natComplex f i h_defined where
  f p := ordinaryInclusionComponent f i p
  comm' := sorry

/-- The canonical inclusion of ordinary relative forms into logarithmic relative forms. -/
noncomputable def ordinaryInclusion {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    ordinaryComplex f ⟶ complex f i h_defined :=
  HomologicalComplex.extendMap (ordinaryInclusionNat f i h_defined) embeddingUpNat

/-- The unshifted pushed-forward de Rham complex of Y/S. -/
noncomputable abbrev divisorUnshiftedComplex {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X) :
    CochainComplex (Modules f.toLRSHom.toShHom) ℤ :=
  ((RingedSpace.DeRham.pushforwardComplex (divisorSquare f i)).obj
    (RingedSpace.DeRham.complex (i ≫ f).toLRSHom.toShHom)).extend embeddingUpNat

/-- The degree arithmetic identifying degree p with shifted degree p + 1. -/
theorem degree_shift (p : ℕ) : (p : ℤ) = ((p + 1 : ℕ) : ℤ) + (-1 : ℤ) := sorry

/-- The natural-degree embedding sends p to its integer coercion. -/
theorem embeddingUpNat_eq (p : ℕ) : embeddingUpNat.f p = (p : ℤ) := sorry

/-- The actual restriction of ordinary p-forms to Y, placed in degree p + 1 of the
shifted divisor complex. -/
noncomputable def divisorRestriction {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    (p : ℕ) : RingedSpace.DeRham.term f.toLRSHom.toShHom p ⟶
      (divisorComplex f i).X ((p + 1 : ℕ) : ℤ) :=
  (RingedSpace.DeRham.map (divisorSquare f i)).f p ≫
    (((RingedSpace.DeRham.pushforwardComplex (divisorSquare f i)).obj
      (RingedSpace.DeRham.complex (i ≫ f).toLRSHom.toShHom)).extendXIso
        embeddingUpNat (embeddingUpNat_eq p)).inv ≫
    ((divisorUnshiftedComplex f i).shiftFunctorObjXIso (-1 : ℤ)
      ((p + 1 : ℕ) : ℤ) (p : ℤ) (degree_shift p)).inv

/-- The divisor restriction is induced by the actual de Rham map for Y ⟶ X ⟶ S. -/
theorem divisorRestriction_spec {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    (p : ℕ) :
    divisorRestriction f i p =
      (RingedSpace.DeRham.map (divisorSquare f i)).f p ≫
        (((RingedSpace.DeRham.pushforwardComplex (divisorSquare f i)).obj
          (RingedSpace.DeRham.complex (i ≫ f).toLRSHom.toShHom)).extendXIso
            embeddingUpNat (embeddingUpNat_eq p)).inv ≫
        ((divisorUnshiftedComplex f i).shiftFunctorObjXIso (-1 : ℤ)
          ((p + 1 : ℕ) : ℤ) (p : ℤ) (degree_shift p)).inv := sorry

/-- A residue component has the canonical formula when it kills ordinary generators and sends
dlog(a) ∧ ω to the actual restriction of ω to Y. -/
def IsResidueComponent {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (p : ℕ)
    (r : (term f i (p + 1) : Modules f.toLRSHom.toShHom) ⟶
      (divisorComplex f i).X ((p + 1 : ℕ) : ℤ)) : Prop :=
  (∀ g : OrdinaryGenerator f (p + 1),
      ((r.val.app (Opposite.op g.1)).hom
        (generatorLift f i (p + 1) (Sum.inl g))) = 0) ∧
    ∀ g : DlogGenerator f i p,
      ((r.val.app (Opposite.op g.1)).hom
        (generatorLift f i (p + 1) (Sum.inr g))) =
      (((divisorRestriction f i p).val.app (Opposite.op g.1)).hom g.2.2.2.val)

/-- Definability gives a unique residue component with the restriction and ordinary-generator
formulas. -/
theorem existsUnique_residueComponent {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (p : ℕ) :
    ∃! r : (term f i (p + 1) : Modules f.toLRSHom.toShHom) ⟶
        (divisorComplex f i).X ((p + 1 : ℕ) : ℤ),
      IsResidueComponent f i p r := sorry

/-- The canonical degree-p + 1 residue component. -/
noncomputable def residueComponent {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (p : ℕ) :
    (term f i (p + 1) : Modules f.toLRSHom.toShHom) ⟶
      (divisorComplex f i).X ((p + 1 : ℕ) : ℤ) :=
  Classical.choose (existsUnique_residueComponent f i h_defined p)

/-- The residue component kills ordinary generators and is restriction on logarithmic generators. -/
theorem residueComponent_spec {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (p : ℕ) :
    IsResidueComponent f i p (residueComponent f i h_defined p) := sorry

/-- A residue component satisfying the actual restriction formula is the canonical one. -/
theorem residueComponent_unique {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (p : ℕ)
    (r : (term f i (p + 1) : Modules f.toLRSHom.toShHom) ⟶
      (divisorComplex f i).X ((p + 1 : ℕ) : ℤ))
    (hr : IsResidueComponent f i p r) : r = residueComponent f i h_defined p := sorry

/-- In every positive degree, the kernel of the canonical residue is exactly the image of
ordinary relative forms. -/
theorem residueComponent_kernel {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) (p : ℕ) :
    kernelSubobject (residueComponent f i h_defined p) =
      imageSubobject (ordinaryInclusionComponent f i (p + 1)) := sorry

/-- The canonical logarithmic residue morphism, zero in nonpositive degrees and induced by
the uniquely specified residue components in positive degrees. -/
noncomputable def residue {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    complex f i h_defined ⟶ divisorComplex f i where
  f
    | Int.ofNat 0 => 0
    | Int.ofNat (p + 1) =>
        ((natComplex f i h_defined).extendXIso embeddingUpNat
          (embeddingUpNat_eq (p + 1))).hom ≫ residueComponent f i h_defined p
    | Int.negSucc _ => 0
  comm' := sorry

/-- The ordinary inclusion followed by the canonical residue is zero. -/
theorem ordinaryInclusion_residue {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    ordinaryInclusion f i h_defined ≫ residue f i h_defined = 0 := sorry

/-- The canonical logarithmic residue sequence determined by h_defined. -/
noncomputable def canonicalSequence {S X Y : Scheme.{u}} {f : X ⟶ S} {i : Y ⟶ X}
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    ShortComplex (CochainComplex (Modules f.toLRSHom.toShHom) ℤ) :=
  ShortComplex.mk (ordinaryInclusion f i h_defined) (residue f i h_defined)
    (ordinaryInclusion_residue f i h_defined)

/-- The first term of the canonical sequence is the ordinary relative de Rham complex. -/
theorem canonicalSequence_X₁ {S X Y : Scheme.{u}} {f : X ⟶ S} {i : Y ⟶ X}
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    (canonicalSequence h_defined).X₁ = ordinaryComplex f := sorry

/-- The middle term is the generated logarithmic de Rham complex. -/
theorem canonicalSequence_X₂ {S X Y : Scheme.{u}} {f : X ⟶ S} {i : Y ⟶ X}
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    (canonicalSequence h_defined).X₂ = complex f i h_defined := sorry

/-- The third term is the shifted pushed-forward relative de Rham complex of Y. -/
theorem canonicalSequence_X₃ {S X Y : Scheme.{u}} {f : X ⟶ S} {i : Y ⟶ X}
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    (canonicalSequence h_defined).X₃ = divisorComplex f i := sorry

/-- The canonical residue sequence from ordinary forms through logarithmic forms to the
shifted divisor de Rham complex is short exact. -/
theorem canonicalSequence_shortExact {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] (h_defined : IsDefined f i) :
    (canonicalSequence h_defined).ShortExact := sorry

end Canonical

end AlgebraicGeometry.RingedSpace.DeRham.LogPole
