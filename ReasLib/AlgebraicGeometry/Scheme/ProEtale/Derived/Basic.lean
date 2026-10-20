module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Constant
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.GeneratedSubobject
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Completeness
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ProEtale.Reduction
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.IdealPower

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.DerivedCategory
open CategoryTheory.Sheaf
open AlgebraicGeometry
open Opposite
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme

/-- Sheaves of `Λ`-modules on the small pro-étale site of `X`. -/
abbrev ProetaleModuleSheaf (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    [HasWeakSheafify (ProEt.topology X) (ModuleCat.{v} Λ)] :=
  Sheaf (ProEt.topology X) (ModuleCat.{v} Λ)

/-- `ProetaleModuleSheaf` is the category of sheaves of `Λ`-modules on `X_proétale`. -/
theorem proetaleModuleSheaf_eq (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    [HasWeakSheafify (ProEt.topology X) (ModuleCat.{v} Λ)] :
    ProetaleModuleSheaf X Λ = Sheaf (ProEt.topology X) (ModuleCat.{v} Λ) := sorry

/-- The unbounded derived category of sheaves of `Λ`-modules on the small pro-étale site of `X`. -/
abbrev ProetaleDerived (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    [HasWeakSheafify (ProEt.topology X) (ModuleCat.{v} Λ)]
    [Abelian (ProetaleModuleSheaf X Λ)]
    [HasDerivedCategory (ProetaleModuleSheaf X Λ)] :=
  DerivedCategory (ProetaleModuleSheaf X Λ)

/-- The ambient derived-category owner for `ProetaleDerived` is the canonical derived category of
sheaves of `Λ`-modules on the small pro-étale site. -/
theorem proetaleDerived_def (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    [HasWeakSheafify (ProEt.topology X) (ModuleCat.{v} Λ)]
    [Abelian (ProetaleModuleSheaf X Λ)]
    [HasDerivedCategory (ProetaleModuleSheaf X Λ)] :
    ProetaleDerived X Λ = DerivedCategory (ProetaleModuleSheaf X Λ) := sorry

namespace ProetaleDerived

/-- The constant sheaf of commutative rings with value `Λ` on `X_proétale`. -/
abbrev constantCoefficientRing (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    [HasWeakSheafify (ProEt.topology X) CommRingCat.{v}] :
    Sheaf (ProEt.topology X) CommRingCat.{v} :=
  (constantSheaf (ProEt.topology X) CommRingCat.{v}).obj (CommRingCat.of Λ)

/-- The underlying ring sheaf of `constantCoefficientRing` is the constant `RingCat` sheaf
with value `Λ`. -/
def constantCoefficientRing_ringSheafIso (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    [HasWeakSheafify (ProEt.topology X) CommRingCat.{v}]
    [HasWeakSheafify (ProEt.topology X) RingCat.{v}]
    [(ProEt.topology X).HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
    [(ProEt.topology X).PreservesSheafification (forget₂ CommRingCat.{v} RingCat.{v})] :
    Sheaf.ringSheafOfComm (constantCoefficientRing X Λ) ≅
      (constantSheaf (ProEt.topology X) RingCat.{v}).obj (RingCat.of Λ) :=
  (constantCommuteCompose (ProEt.topology X) (forget₂ CommRingCat.{v} RingCat.{v})).app
    (CommRingCat.of Λ)

/-- The comparison isomorphism identifies the underlying ring sheaf of `constantCoefficientRing`
with the constant `RingCat` sheaf of `Λ`. -/
theorem constantCoefficientRing_ringSheafIso_hom_eq
    (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    [HasWeakSheafify (ProEt.topology X) CommRingCat.{v}]
    [HasWeakSheafify (ProEt.topology X) RingCat.{v}]
    [(ProEt.topology X).HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
    [(ProEt.topology X).PreservesSheafification (forget₂ CommRingCat.{v} RingCat.{v})] :
    (constantCoefficientRing_ringSheafIso X Λ).hom =
      ((constantCommuteCompose (ProEt.topology X)
          (forget₂ CommRingCat.{v} RingCat.{v})).app (CommRingCat.of Λ)).hom := sorry

/-- The canonical view of a pro-étale `Λ`-module sheaf as a module over the constant ring sheaf
of `Λ`, transported to the commutative-ring presentation used by ringed-site derived completeness. -/
def toConstantModuleFunctor (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    [HasWeakSheafify (ProEt.topology X) (ModuleCat.{v} Λ)]
    [HasWeakSheafify (ProEt.topology X) CommRingCat.{v}]
    [HasWeakSheafify (ProEt.topology X) RingCat.{v}]
    [HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{v}]
    [(ProEt.topology X).WEqualsLocallyBijective RingCat.{v}]
    [(ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [(ProEt.topology X).HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
    [(ProEt.topology X).HasSheafCompose (forget₂ RingCat.{v} AddCommGrpCat.{v})]
    [(ProEt.topology X).PreservesSheafification (forget₂ CommRingCat.{v} RingCat.{v})] :
    ProetaleModuleSheaf X Λ ⥤
      RingedSite.ModuleCat
        (RingedSite.ofCommRingSheaf (ProEt.topology X) (constantCoefficientRing X Λ)) :=
  ConstantModule.sheafFunctor ⋙
    SheafOfModules.restrictScalars (constantCoefficientRing_ringSheafIso X Λ).hom

/-- On objects, `toConstantModuleFunctor` is the constant-module sheaf view followed by restriction
of scalars along `constantCoefficientRing_ringSheafIso`. -/
theorem toConstantModuleFunctor_obj (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    [HasWeakSheafify (ProEt.topology X) (ModuleCat.{v} Λ)]
    [HasWeakSheafify (ProEt.topology X) CommRingCat.{v}]
    [HasWeakSheafify (ProEt.topology X) RingCat.{v}]
    [HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{v}]
    [(ProEt.topology X).WEqualsLocallyBijective RingCat.{v}]
    [(ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [(ProEt.topology X).HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
    [(ProEt.topology X).HasSheafCompose (forget₂ RingCat.{v} AddCommGrpCat.{v})]
    [(ProEt.topology X).PreservesSheafification (forget₂ CommRingCat.{v} RingCat.{v})]
    (F : ProetaleModuleSheaf X Λ) :
    (toConstantModuleFunctor X Λ).obj F =
      (SheafOfModules.restrictScalars (constantCoefficientRing_ringSheafIso X Λ).hom).obj
        F.toConstantModuleSheaf := sorry

variable {X : Scheme.{u}} {Λ : Type v} [CommRing Λ]
variable [HasWeakSheafify (ProEt.topology X) (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ))]

-- Local declaration justification (instance diamond): `Sheaf` is a `FullSubcategory`,
-- so `HasZeroMorphisms`/`Preadditive` are synthesized from that embedding, while
-- derived tensor and `mapDerivedCategory` are typed using `Abelian.toPreadditive`.
attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory
attribute [-instance] Preadditive.fullSubcategory

section TensorReduction

variable [MonoidalCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ))]
variable [MonoidalPreadditive (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ))]
variable [∀ (K L : CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ)) ℤ),
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ))) (ComplexShape.up ℤ)]
variable [h_derivedTensor :
  @DerivedTensor.Right.Has (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ)) _ _ _ _ _ _]

/-- Derived reduction of `K` modulo `I` is the derived tensor
`K ⊗ᴸ underline{Λ / I}` on `X_proétale`. -/
def reduction (I : Ideal Λ) (K : ProetaleDerived X Λ) : ProetaleDerived X Λ :=
  K ⊗ᴸ (DerivedCategory.singleFunctor (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ)) 0).obj
      (constantIdealQuotientSheaf (ProEt.topology X) I)

/-- Reduction modulo `I` is derived tensor with the constant sheaf of `Λ / I`. -/
theorem reduction_eq (I : Ideal Λ) (K : ProetaleDerived X Λ) :
    reduction I K =
      K ⊗ᴸ (DerivedCategory.singleFunctor (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ)) 0).obj
          (constantIdealQuotientSheaf (ProEt.topology X) I) := sorry

end TensorReduction

variable [HasWeakSheafify (ProEt.topology X) CommRingCat.{v}]
variable [HasWeakSheafify (ProEt.topology X) RingCat.{v}]
variable [HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{v}]
variable [(ProEt.topology X).WEqualsLocallyBijective RingCat.{v}]
variable [(ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{v}]
variable [(ProEt.topology X).HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
variable [(ProEt.topology X).HasSheafCompose (forget₂ RingCat.{v} AddCommGrpCat.{v})]
variable [(ProEt.topology X).PreservesSheafification (forget₂ CommRingCat.{v} RingCat.{v})]
variable [UnivLE.{u + 1, v}]

/-- The standard derived-category structure on modules over the constant ring sheaf of `Λ`. -/
@[reducible] noncomputable def hasDerivedCategory_constantCoefficient :
    HasDerivedCategory
      (RingedSite.ModuleCat
        (RingedSite.ofCommRingSheaf (ProEt.topology X) (constantCoefficientRing X Λ))) :=
  RingedSite.Hom.moduleCat_hasDerivedCategory
    (RingedSite.ofCommRingSheaf (ProEt.topology X) (constantCoefficientRing X Λ))

/-- `toConstantModuleFunctor` is additive. -/
theorem toConstantModuleFunctor_additive :
    (toConstantModuleFunctor X Λ).Additive := sorry

/-- `toConstantModuleFunctor` preserves finite limits. -/
theorem toConstantModuleFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (toConstantModuleFunctor X Λ) := sorry

/-- `toConstantModuleFunctor` preserves finite colimits. -/
theorem toConstantModuleFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (toConstantModuleFunctor X Λ) := sorry

/-- The derived constant-ringed-site image of an object of `D(X_proétale, Λ)`. -/
def toConstantModuleDerived (K : ProetaleDerived X Λ) :
    RingedSite.Hom.ModuleDerived
      (RingedSite.ofCommRingSheaf (ProEt.topology X) (constantCoefficientRing X Λ)) :=
  (@Functor.mapDerivedCategory
    (ProetaleModuleSheaf X Λ) _ _ _
    (RingedSite.ModuleCat
      (RingedSite.ofCommRingSheaf (ProEt.topology X) (constantCoefficientRing X Λ)))
    _ _ (hasDerivedCategory_constantCoefficient (X := X) (Λ := Λ))
    (toConstantModuleFunctor X Λ)
    toConstantModuleFunctor_additive
    toConstantModuleFunctor_preservesFiniteLimits
    toConstantModuleFunctor_preservesFiniteColimits).obj K

/-- The derived constant-module view is the functor on derived categories induced by
`toConstantModuleFunctor`. -/
theorem toConstantModuleDerived_eq (K : ProetaleDerived X Λ) :
    toConstantModuleDerived K =
      (@Functor.mapDerivedCategory
        (ProetaleModuleSheaf X Λ) _ _ _
        (RingedSite.ModuleCat
          (RingedSite.ofCommRingSheaf (ProEt.topology X) (constantCoefficientRing X Λ)))
        _ _ (hasDerivedCategory_constantCoefficient (X := X) (Λ := Λ))
        (toConstantModuleFunctor X Λ)
        toConstantModuleFunctor_additive
        toConstantModuleFunctor_preservesFiniteLimits
        toConstantModuleFunctor_preservesFiniteColimits).obj K := sorry

/-- The sheafification map from the constant `Λ`-presheaf to `constantCoefficientRing`. -/
abbrev constantCoefficientToSheafify :
    (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of Λ) ⟶
      (constantCoefficientRing X Λ).obj :=
  toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of Λ))

variable [LocallySmall
    (SheafOfModules (Sheaf.ringSheafOfComm (constantCoefficientRing X Λ)))]
variable [WellPowered
    (SheafOfModules (Sheaf.ringSheafOfComm (constantCoefficientRing X Λ)))]

/-- The constant ideal sheaf on `X_proétale` associated to `I ⊆ Λ`, as a subobject of the
structure module of `constantCoefficientRing`. -/
def constantCoefficientIdeal (I : Ideal Λ) :
    Subobject
      (SheafOfModules.RingedSite.unitModule (ProEt.topology X)
        (constantCoefficientRing X Λ)) :=
  SheafOfModules.Subobject.generatedBySections
    (SheafOfModules.RingedSite.unitModule (ProEt.topology X)
      (constantCoefficientRing X Λ))
    (fun p : X.ProEt × {a // a ∈ I} ↦ p.1)
    (fun p ↦
      ((forget₂ CommRingCat.{v} RingCat.{v}).map
        (constantCoefficientToSheafify.app (op p.1))).hom (p.2 : Λ))

/-- The constant coefficient ideal is generated by the constant sections of elements of `I`. -/
theorem constantCoefficientIdeal_eq (I : Ideal Λ) :
    constantCoefficientIdeal I =
      SheafOfModules.Subobject.generatedBySections
        (SheafOfModules.RingedSite.unitModule (ProEt.topology X)
          (constantCoefficientRing X Λ))
        (fun p : X.ProEt × {a // a ∈ I} ↦ p.1)
        (fun p ↦
          ((forget₂ CommRingCat.{v} RingCat.{v}).map
            (constantCoefficientToSheafify.app (op p.1))).hom (p.2 : Λ)) := sorry

/-- An object of `D(X_proétale, Λ)` is derived complete with respect to `I` when its
constant-ringed-site image is derived complete with respect to the constant ideal sheaf of `I`. -/
def IsDerivedCompleteWithRespectTo (K : ProetaleDerived X Λ) (I : Ideal Λ) : Prop :=
  RingedSite.Hom.ModuleDerived.IsDerivedCompleteWithRespectTo
    (toConstantModuleDerived K) (constantCoefficientIdeal I)

/-- Derived completeness on `D(X_proétale, Λ)` is derived completeness of the
constant-ringed-site image with respect to the ideal sheaf generated by `I`. -/
theorem isDerivedCompleteWithRespectTo_iff (K : ProetaleDerived X Λ) (I : Ideal Λ) :
    IsDerivedCompleteWithRespectTo K I ↔
      RingedSite.Hom.ModuleDerived.IsDerivedCompleteWithRespectTo
        (toConstantModuleDerived K) (constantCoefficientIdeal I) := sorry

end ProetaleDerived

end AlgebraicGeometry.Scheme
