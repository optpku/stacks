module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Cohomology.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.LerayHirsch
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.CanonicalAction
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Equiv
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.LinearAlgebra.Basis.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open DerivedCategory.DerivedTensor.Right.Monoidal
open RingedSite.Hom
open AlgebraicGeometry.Scheme.DeRham.DerivedPushforward
open scoped DerivedTensorProduct MonoidalCategory TensorProduct

-- Local instance justification (defeq pin): these constructions use the canonical coefficient-site derived-category presentation and the total-derived shift comparisons required by shiftedHomMap and commShiftIso.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory
  AlgebraicGeometry.Scheme.DeRham.CanonicalAction.globalCommShift
  AlgebraicGeometry.Scheme.DeRham.CanonicalTensor.pushforwardCommShift

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.LerayHirsch

variable {X Y S : Scheme.{u}} {f : X ⟶ Y} {a : X ⟶ S} {b : Y ⟶ S}

/-- The coefficient-sheaf module category carries its canonical tensor product. -/
@[reducible]
noncomputable def coefficientSheafMonoidal (a : X ⟶ S) :
    MonoidalCategory
      (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom).ModuleCat :=
  SheafOfModules.RingedSite.moduleMonoidalCategory
    (RingedSpace.DeRham.coefficients a.toLRSHom.toShHom)

/-- Cochain complexes of coefficient-sheaf modules carry the standard totalized tensor product. -/
@[reducible]
noncomputable def coefficientComplexMonoidal (a : X ⟶ S) :
    MonoidalCategory
      (CochainComplex
        (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom).ModuleCat ℤ) :=
  -- Local instance justification (defeq pin): the totalized tensor constructor must use the explicit coefficient-sheaf presentation.
  letI := coefficientSheafMonoidal a
  @HomologicalComplex.monoidalCategory
    (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom).ModuleCat
    inferInstance (coefficientSheafMonoidal a) inferInstance inferInstance inferInstance
    inferInstance ℤ inferInstance (ComplexShape.up ℤ) inferInstance
    (fun X Y ↦ SheafOfModules.RingedSite.IntGraded.hasTensor X Y)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance

/-- Lax monoidality of derived global sections for the explicit coefficient-complex tensor
presentation. -/
abbrev CoefficientGlobalLaxMonoidal (a : X ⟶ S)
    [targetMonoidal : MonoidalCategory (coefficientDerived a)] :=
  @Functor.LaxMonoidal
    (CochainComplex
      (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom).ModuleCat ℤ)
    _ (coefficientComplexMonoidal a) (coefficientDerived a) _ targetMonoidal
    (globalDerivedFunctor a)

/-- Cup product on the left by `ξ`, after pulling a class back along the triangle. -/
noncomputable def leftCupPullback (sq : CommSq f a b (𝟙 S))
    [IsAffine S]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (Cohomology.coefficientHom sq))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))]
    [MonoidalCategory (coefficientDerived a)]
    [(DerivedCategory.Qh : HomotopyCategory (coefficientModules a) (ComplexShape.up ℤ) ⥤
      coefficientDerived a).Monoidal]
    [globalLax : CoefficientGlobalLaxMonoidal a]
    {n : ℕ} (q : ℤ) (ξ : cohomology a (n : ℤ)) :
    Cohomology.overBase b (q - (n : ℤ)) ⟶ Cohomology.overBase a q :=
  -- Local instance justification (defeq pin): the cup-product API requires the explicit coefficient-sheaf presentation as an instance.
  letI := coefficientSheafMonoidal a
  -- Local instance justification (defeq pin): the cup-product API requires the explicit coefficient-complex presentation as an instance.
  letI := coefficientComplexMonoidal a
  -- Local instance justification (proof-local temporary data): the generic cup-product API consumes the named lax monoidal interface through typeclass syntax.
  letI : (globalDerivedFunctor a).LaxMonoidal := globalLax
  ModuleCat.ofHom
    (R := Scheme.globalSectionsRing S)
    (X := Cohomology.overBase b (q - (n : ℤ)))
    (Y := Cohomology.overBase a q)
    { toFun := fun x ↦
        (Cohomology.castDegree a
          ((add_comm (n : ℤ) (q - (n : ℤ))).trans
            (sub_add_cancel q (n : ℤ)))).hom
          ((cohomologyCupProduct a (n : ℤ) (q - (n : ℤ))).hom
            (ξ ⊗ₜ (Cohomology.pullback sq (q - (n : ℤ))).hom x))
      map_add' := sorry
      map_smul' := sorry }

/-- The left cup-pullback map evaluates as `x ↦ ξ ∪ f⁺a`, with the canonical degree
transport from `n + (q - n)` to `q`. -/
theorem leftCupPullback_apply (sq : CommSq f a b (𝟙 S))
    [IsAffine S]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (Cohomology.coefficientHom sq))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))]
    [MonoidalCategory (coefficientDerived a)]
    [(DerivedCategory.Qh : HomotopyCategory (coefficientModules a) (ComplexShape.up ℤ) ⥤
      coefficientDerived a).Monoidal]
    [CoefficientGlobalLaxMonoidal a]
    {n : ℕ} (q : ℤ)
    (ξ : cohomology a (n : ℤ)) (x : cohomology b (q - (n : ℤ))) :
    (leftCupPullback sq q ξ).hom x =
      (Cohomology.castDegree a
        ((add_comm (n : ℤ) (q - (n : ℤ))).trans
          (sub_add_cancel q (n : ℤ)))).hom
        ((cohomologyCupProduct a (n : ℤ) (q - (n : ℤ))).hom
          (ξ ⊗ₜ (Cohomology.pullback sq (q - (n : ℤ))).hom x)) := sorry

/-- The degree-`q` source of the Leray–Hirsch map. -/
noncomputable abbrev degreeSource (b : Y ⟶ S) {N : ℕ}
    [IsAffine S]
    (n : Fin N → ℕ) (q : ℤ) : ModuleCat.{u} (Scheme.globalSectionsRing S) :=
  ModuleCat.of (Scheme.globalSectionsRing S)
    (DirectSum (Fin N) fun i ↦ Cohomology.overBase b (q - (n i : ℤ)))

/-- The degree source is the finite biproduct of the shifted cohomology groups of `Y/S`. -/
theorem degreeSource_def (b : Y ⟶ S) {N : ℕ} [IsAffine S]
    (n : Fin N → ℕ) (q : ℤ) :
    degreeSource b n q = ModuleCat.of (Scheme.globalSectionsRing S)
      (DirectSum (Fin N) fun i ↦ Cohomology.overBase b (q - (n i : ℤ))) := sorry

/-- The degree-`q` Leray–Hirsch map whose `i`-th component is cup product by `ξ i` after
pullback from `Y/S`. -/
noncomputable def cohomologyMap (sq : CommSq f a b (𝟙 S))
    [IsAffine S]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (Cohomology.coefficientHom sq))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))]
    [MonoidalCategory (coefficientDerived a)]
    [(DerivedCategory.Qh : HomotopyCategory (coefficientModules a) (ComplexShape.up ℤ) ⥤
      coefficientDerived a).Monoidal]
    [CoefficientGlobalLaxMonoidal a]
    {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, cohomology a (n i : ℤ)) (q : ℤ) :
    degreeSource b n q ⟶ Cohomology.overBase a q :=
  ModuleCat.ofHom (R := Scheme.globalSectionsRing S)
    (X := degreeSource b n q) (Y := Cohomology.overBase a q)
    (DirectSum.toModule (Scheme.globalSectionsRing S) (Fin N)
      (Cohomology.overBase a q) fun i ↦ (leftCupPullback sq q (ξ i)).hom)

/-- On the `i`-th shifted summand, `cohomologyMap` is cup product by `ξ i` after pullback. -/
theorem cohomologyMap_lof (sq : CommSq f a b (𝟙 S))
    [IsAffine S]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (Cohomology.coefficientHom sq))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))]
    [MonoidalCategory (coefficientDerived a)]
    [(DerivedCategory.Qh : HomotopyCategory (coefficientModules a) (ComplexShape.up ℤ) ⥤
      coefficientDerived a).Monoidal]
    [CoefficientGlobalLaxMonoidal a]
    {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, cohomology a (n i : ℤ)) (q : ℤ) (i : Fin N) :
    (cohomologyMap sq n ξ q).hom.comp
        (DirectSum.lof (Scheme.globalSectionsRing S) (Fin N)
          (fun j ↦ Cohomology.overBase b (q - (n j : ℤ))) i) =
      (leftCupPullback sq q (ξ i)).hom := sorry

/-- The commutative square from the fiber of `f` at `y` to the triangle over `S`. -/
theorem fiberSquare_comm (sq : CommSq f a b (𝟙 S)) (y : Y) :
    f.fiberι y ≫ a =
      f.fiberToSpecResidueField y ≫ (Y.fromSpecResidueField y ≫ b) := sorry

/-- The square used to restrict an absolute de Rham class to the fiber of `f` at `y`. -/
theorem fiberSquare (sq : CommSq f a b (𝟙 S)) (y : Y) :
    CommSq (f.fiberι y) (f.fiberToSpecResidueField y) a
      (Y.fromSpecResidueField y ≫ b) := sorry

/-- The fiber square has the source commutativity supplied by `fiberSquare_comm`. -/
theorem fiberSquare_w (sq : CommSq f a b (𝟙 S)) (y : Y) :
    (fiberSquare sq y).w = fiberSquare_comm sq y := sorry

/-- The image of an absolute relative de Rham class on the residue-field fiber at `y`. -/
noncomputable def fiberClass (sq : CommSq f a b (𝟙 S)) (y : Y) (q : ℤ)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (Cohomology.coefficientHom (fiberSquare sq y)))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        (f.fiberToSpecResidueField y).toLRSHom.toShHom))]
    (ξ : cohomology a q) :
    cohomologyOverAffineBase (f.fiberToSpecResidueField y) q :=
  (Cohomology.restrictedPullback (fiberSquare sq y) q).hom ξ

/-- `fiberClass` is evaluation of the canonical cohomological pullback to the residue fiber. -/
theorem fiberClass_spec (sq : CommSq f a b (𝟙 S)) (y : Y) (q : ℤ)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (Cohomology.coefficientHom (fiberSquare sq y)))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        (f.fiberToSpecResidueField y).toLRSHom.toShHom))]
    (ξ : cohomology a q) :
    fiberClass sq y q ξ =
      (Cohomology.restrictedPullback (fiberSquare sq y) q).hom ξ := sorry

/-- The total graded de Rham cohomology of a residue-field fiber. -/
abbrev fiberCohomology (f : X ⟶ Y) (y : Y) : ModuleCat.{u} (Y.residueField y) :=
  ModuleCat.of (Y.residueField y)
    (DirectSum ℤ fun q ↦ cohomologyOverAffineBase (f.fiberToSpecResidueField y) q)

/-- Total fiber cohomology is the direct sum of its integer-graded pieces. -/
theorem fiberCohomology_def (f : X ⟶ Y) (y : Y) :
    fiberCohomology f y =
      ModuleCat.of (Y.residueField y)
        (DirectSum ℤ fun q ↦ cohomologyOverAffineBase (f.fiberToSpecResidueField y) q) := sorry

/-- The absolute classes form a basis on every residue-field fiber when their homogeneous
images give a basis of total fiber de Rham cohomology. -/
def IsAbsoluteFiberwiseBasis (sq : CommSq f a b (𝟙 S)) {N : ℕ}
    (n : Fin N → ℕ) (ξ : ∀ i, cohomology a (n i : ℤ))
    [∀ y : Y, Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (Cohomology.coefficientHom (fiberSquare sq y)))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        (f.fiberToSpecResidueField y).toLRSHom.toShHom))] : Prop :=
  ∀ y : Y, ∃ e : Module.Basis (Fin N) (Y.residueField y) (fiberCohomology f y),
    ∀ i, e i = DirectSum.of
      (fun q : ℤ ↦ cohomologyOverAffineBase (f.fiberToSpecResidueField y) q)
      (n i : ℤ) (fiberClass sq y (n i : ℤ) (ξ i))

/-- The absolute fiberwise-basis condition is the existence, on every residue fiber, of a basis
whose `i`-th vector is the homogeneous restriction of `ξ i`. -/
theorem isAbsoluteFiberwiseBasis_iff (sq : CommSq f a b (𝟙 S)) {N : ℕ}
    (n : Fin N → ℕ) (ξ : ∀ i, cohomology a (n i : ℤ))
    [∀ y : Y, Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (Cohomology.coefficientHom (fiberSquare sq y)))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        (f.fiberToSpecResidueField y).toLRSHom.toShHom))] :
    IsAbsoluteFiberwiseBasis sq n ξ ↔
      ∀ y : Y, ∃ e : Module.Basis (Fin N) (Y.residueField y) (fiberCohomology f y),
        ∀ i, e i = DirectSum.of
          (fun q : ℤ ↦ cohomologyOverAffineBase (f.fiberToSpecResidueField y) q)
          (n i : ℤ) (fiberClass sq y (n i : ℤ) (ξ i)) := sorry

/-- For a smooth proper triangle over affine schemes, homogeneous absolute de Rham classes
that form a basis on every residue-field fiber induce degreewise Leray–Hirsch isomorphisms. -/
theorem cohomologyMap_isIso {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (a : X ⟶ S) (b : Y ⟶ S) (sq : CommSq f a b (𝟙 S))
    [Smooth f] [IsProper f] [IsAffine Y] [IsAffine S]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (Cohomology.coefficientHom sq))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))]
    [∀ y : Y, Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (Cohomology.coefficientHom (fiberSquare sq y)))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        (f.fiberToSpecResidueField y).toLRSHom.toShHom))]
    [MonoidalCategory (coefficientDerived a)]
    [(DerivedCategory.Qh : HomotopyCategory (coefficientModules a) (ComplexShape.up ℤ) ⥤
      coefficientDerived a).Monoidal]
    [CoefficientGlobalLaxMonoidal a]
    {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, cohomology a (n i : ℤ)) (hξ : IsAbsoluteFiberwiseBasis sq n ξ) :
    ∀ q : ℤ, IsIso (cohomologyMap sq n ξ q) := sorry

/-- The finite biproduct of the negatively shifted de Rham complexes of `Y/S`. -/
noncomputable abbrev overBaseSource {N : ℕ} (b : Y ⟶ S) (n : Fin N → ℕ) :
    ModuleDerived.{u} (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom) :=
  ⨁ fun i ↦ (derivedComplex b)⟦-(n i : ℤ)⟧

/-- The source of the absolute Leray–Hirsch map is the finite biproduct of the indicated
negative shifts. -/
theorem overBaseSource_def {N : ℕ} (b : Y ⟶ S) (n : Fin N → ℕ) :
    overBaseSource b n = ⨁ fun i ↦ (derivedComplex b)⟦-(n i : ℤ)⟧ := rfl

variable (sq : CommSq f a b (𝟙 S))
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{u} (Cohomology.coefficientHom sq))
  (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))]


/-- The `i`-th shifted component: pull back the de Rham complex from `Y/S`, then act by the
absolute class `ξ i` after derived direct image. -/
noncomputable def overBaseComponent {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, cohomology a (n i : ℤ)) (i : Fin N) :
    (derivedComplex b)⟦-(n i : ℤ)⟧ ⟶
      (modulePushforwardDerived.{u} (Cohomology.coefficientHom sq)).obj
        (derivedComplex a) :=
  ShiftedHom.sourceShiftEquiv (derivedComplex b)
    ((modulePushforwardDerived.{u} (Cohomology.coefficientHom sq)).obj
      (derivedComplex a)) (n i : ℤ)
    (Cohomology.derivedPullback sq ≫
      (modulePushforwardDerived.{u}
        (Cohomology.coefficientHom sq)).shiftedHomMap
          (Iso.refl _) (Iso.refl _) (n i : ℤ)
          (CanonicalAction.map a (n i : ℤ) (ξ i)))

/-- The shifted component is the source-shift form of de Rham pullback followed by the
pushed-forward action of `ξ i`. -/
theorem overBaseComponent_def {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, cohomology a (n i : ℤ)) (i : Fin N) :
    overBaseComponent sq n ξ i =
      ShiftedHom.sourceShiftEquiv (derivedComplex b)
        ((modulePushforwardDerived.{u} (Cohomology.coefficientHom sq)).obj
          (derivedComplex a)) (n i : ℤ)
        (Cohomology.derivedPullback sq ≫
          (modulePushforwardDerived.{u}
            (Cohomology.coefficientHom sq)).shiftedHomMap
              (Iso.refl _) (Iso.refl _) (n i : ℤ)
              (CanonicalAction.map a (n i : ℤ) (ξ i))) := sorry

/-- The absolute Leray–Hirsch map assembled from all homogeneous components. -/
noncomputable def overBaseMap {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, cohomology a (n i : ℤ)) :
    overBaseSource b n ⟶
      (modulePushforwardDerived.{u} (Cohomology.coefficientHom sq)).obj
        (derivedComplex a) :=
  biproduct.desc (overBaseComponent sq n ξ)

/-- Restricting the absolute Leray–Hirsch map to its `i`-th biproduct summand recovers the
corresponding shifted component. -/
theorem overBaseMap_ι {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, cohomology a (n i : ℤ)) (i : Fin N) :
    biproduct.ι (fun j ↦ (derivedComplex b)⟦-(n j : ℤ)⟧) i ≫
      overBaseMap sq n ξ = overBaseComponent sq n ξ i := sorry

/-- The absolute derived Leray--Hirsch map: absolute de Rham classes forming a basis on every residue fiber
give an isomorphism from the finite biproduct of negatively shifted `Ωᵈᴿ[Y/S]` to
`Rf_*Ωᵈᴿ[X/S]`. -/
theorem overBaseMap_isIso [Smooth f] [IsProper f]
    [∀ y : Y, Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (Cohomology.coefficientHom (fiberSquare sq y)))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        (f.fiberToSpecResidueField y).toLRSHom.toShHom))]
    {N : ℕ} (n : Fin N → ℕ) (ξ : ∀ i, cohomology a (n i : ℤ))
    (hξ : IsAbsoluteFiberwiseBasis sq n ξ) :
    IsIso (overBaseMap sq n ξ) := sorry

/-- The degree-`q` source of the absolute Leray–Hirsch cohomology map. -/
noncomputable abbrev overBaseCohomologySource {N : ℕ} (b : Y ⟶ S)
    (n : Fin N → ℕ) (q : ℤ) : ModuleCat.{u} (coefficientRing b) :=
  ModuleCat.of (coefficientRing b)
    (DirectSum (Fin N) fun i ↦ cohomology b (q - (n i : ℤ)))

/-- The degreewise source is the direct sum of the shifted de Rham cohomology modules of
`Y/S`. -/
theorem overBaseCohomologySource_def {N : ℕ} (b : Y ⟶ S)
    (n : Fin N → ℕ) (q : ℤ) :
    overBaseCohomologySource b n q = ModuleCat.of (coefficientRing b)
      (DirectSum (Fin N) fun i ↦ cohomology b (q - (n i : ℤ))) := sorry

/-- The `i`-th degree-`q` cohomology component: pull back from `Y/S`, apply the action of
`ξ i`, restrict scalars to the coefficient ring of `Y/S`, and transport the degree to `q`. -/
noncomputable def overBaseCohomologyComponent {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, cohomology a (n i : ℤ)) (q : ℤ) (i : Fin N) :
    cohomology b (q - (n i : ℤ)) ⟶ Cohomology.restricted sq q :=
  Cohomology.restrictedPullback sq (q - (n i : ℤ)) ≫
    (globalSectionsRestriction.{u} (Cohomology.coefficientHom sq)).map
      (CanonicalAction.onCohomology a (n i : ℤ) (q - (n i : ℤ)) (ξ i)) ≫
    eqToHom (congrArg (Cohomology.restricted sq)
      ((add_comm (n i : ℤ) (q - (n i : ℤ))).trans
        (sub_add_cancel q (n i : ℤ))))

/-- The degree-`q` homology realization of the `i`-th shifted derived component, transported
through derived global sections, the shift comparison, and the direct-image comparison. -/
noncomputable def overBaseComponentHomology
    {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, cohomology a (n i : ℤ)) (q : ℤ) (i : Fin N) :
    cohomology b (q - (n i : ℤ)) ⟶ Cohomology.restricted sq q :=
  (((DerivedCategory.homologyFunctor (coefficientModules b) q).mapIso
      (((moduleDerivedGlobalSections.{u}
        (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom)).commShiftIso
          (-(n i : ℤ))).app (derivedComplex b)) ≪≫
    ((DerivedCategory.homologyFunctor (coefficientModules b) 0).shiftIso
      (-(n i : ℤ)) q (q - (n i : ℤ)) (neg_add_eq_sub (n i : ℤ) q)).app
        (globalDerivedObject b)).inv ≫
    (DerivedCategory.homologyFunctor (coefficientModules b) q).map
      ((moduleDerivedGlobalSections.{u}
          (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom)).map
            (overBaseComponent sq n ξ i) ≫
        (Cohomology.derivedGlobalComparisonInv sq).app (derivedComplex a)) ≫
    (Functor.MapDerivedCategory.homologyIso
      (globalSectionsRestriction.{u, u, u, u, u, u} (Cohomology.coefficientHom sq))
      (globalDerivedObject a) q).hom)

/-- The explicit cup-pullback component agrees with the degree-`q` homology realization of
`overBaseComponent`. -/
theorem overBaseCohomologyComponent_eq_homology {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, cohomology a (n i : ℤ)) (q : ℤ) (i : Fin N) :
    overBaseCohomologyComponent sq n ξ q i =
      overBaseComponentHomology sq n ξ q i := sorry

/-- The degree-`q` absolute Leray–Hirsch map assembled from the homogeneous components. -/
noncomputable def overBaseCohomologyMap {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, cohomology a (n i : ℤ)) (q : ℤ) :
    overBaseCohomologySource b n q ⟶ Cohomology.restricted sq q :=
  @ModuleCat.ofHom (coefficientRing b) inferInstance
    (overBaseCohomologySource b n q) (Cohomology.restricted sq q)
    (ModuleCat.isAddCommGroup (overBaseCohomologySource b n q)) (ModuleCat.isModule (overBaseCohomologySource b n q))
    (ModuleCat.isAddCommGroup (Cohomology.restricted sq q)) (ModuleCat.isModule (Cohomology.restricted sq q))
    (DirectSum.toModule (coefficientRing b) (Fin N) (Cohomology.restricted sq q)
      fun i ↦ (overBaseCohomologyComponent sq n ξ q i).hom)

/-- The degree-`q` homology realization of `overBaseMap`, transported through the canonical
finite-biproduct, shift, derived-global-sections, and direct-image comparisons. -/
noncomputable def overBaseMapHomology {N : ℕ} (n : Fin N → ℕ)
    [(moduleDerivedGlobalSections.{u}
      (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom)).Additive]
    (ξ : ∀ i, cohomology a (n i : ℤ)) (q : ℤ) :
    overBaseCohomologySource b n q ⟶ Cohomology.restricted sq q :=
  (DirectSum.linearEquivFunOnFintype (coefficientRing b) (Fin N)
      (fun i ↦ cohomology b (q - (n i : ℤ)))).toModuleIso.hom ≫
    (ModuleCat.biproductIsoPi
      (fun i ↦ cohomology b (q - (n i : ℤ)))).inv ≫
    biproduct.map (fun i ↦
      (((DerivedCategory.homologyFunctor (coefficientModules b) q).mapIso
          (((moduleDerivedGlobalSections.{u}
            (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom)).commShiftIso
              (-(n i : ℤ))).app (derivedComplex b)) ≪≫
        ((DerivedCategory.homologyFunctor (coefficientModules b) 0).shiftIso
          (-(n i : ℤ)) q (q - (n i : ℤ)) (neg_add_eq_sub (n i : ℤ) q)).app
            (globalDerivedObject b)).inv)) ≫
    (((moduleDerivedGlobalSections.{u}
      (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom)) ⋙
        DerivedCategory.homologyFunctor (coefficientModules b) q).mapBiproduct
          (fun i ↦ (derivedComplex b)⟦-(n i : ℤ)⟧)).inv ≫
    (DerivedCategory.homologyFunctor (coefficientModules b) q).map
      ((moduleDerivedGlobalSections.{u}
          (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom)).map
            (overBaseMap sq n ξ) ≫
        (Cohomology.derivedGlobalComparisonInv sq).app (derivedComplex a)) ≫
    (Functor.MapDerivedCategory.homologyIso
      (globalSectionsRestriction.{u, u, u, u, u, u} (Cohomology.coefficientHom sq))
      (globalDerivedObject a) q).hom

/-- On the `i`-th direct-sum generator, the degreewise Leray–Hirsch map is its canonical
cohomological component. -/
theorem overBaseCohomologyMap_lof {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, cohomology a (n i : ℤ)) (q : ℤ) (i : Fin N) :
    (overBaseCohomologyMap sq n ξ q).hom.comp
        (DirectSum.lof (coefficientRing b) (Fin N)
          (fun j ↦ cohomology b (q - (n j : ℤ))) i) =
      (overBaseCohomologyComponent sq n ξ q i).hom := sorry

/-- The explicit direct-sum cohomology map is the degree-`q` homology realization of
`overBaseMap` through the canonical finite-biproduct and shift comparisons. -/
theorem overBaseCohomologyMap_eq_homology {N : ℕ} (n : Fin N → ℕ)
    [(moduleDerivedGlobalSections.{u}
      (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom)).Additive]
    (ξ : ∀ i, cohomology a (n i : ℤ)) (q : ℤ) :
    overBaseCohomologyMap sq n ξ q = overBaseMapHomology sq n ξ q := sorry

/-- The `i`-th component sends `η` to
`ξ i ∪ f⁺η`, with the canonical degree transport. -/
theorem overBaseCohomologyComponent_apply
    {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, cohomology a (n i : ℤ)) (q : ℤ) (i : Fin N)
    (η : cohomology b (q - (n i : ℤ))) :
    (overBaseCohomologyComponent sq n ξ q i).hom η =
      (eqToHom (congrArg (Cohomology.restricted sq)
        ((add_comm (n i : ℤ) (q - (n i : ℤ))).trans
          (sub_add_cancel q (n i : ℤ))))).hom
        ((CanonicalAction.cupMorphism a (n i : ℤ) (q - (n i : ℤ))).hom
          (ξ i ⊗ₜ (Cohomology.restrictedPullback sq
            (q - (n i : ℤ))).hom η)) := sorry

/-- The degreewise absolute Leray--Hirsch map: in every degree, the map
`(η i) ↦ ∑ i, ξ i ∪ f⁺(η i)` is an isomorphism from the shifted de Rham
cohomology of `Y/S` to the scalar-restricted de Rham cohomology of `X/S`. -/
theorem overBaseCohomologyMap_isIso [Smooth f] [IsProper f]
    [∀ y : Y, Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (Cohomology.coefficientHom (fiberSquare sq y)))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        (f.fiberToSpecResidueField y).toLRSHom.toShHom))]
    {N : ℕ} (n : Fin N → ℕ) (ξ : ∀ i, cohomology a (n i : ℤ))
    (hξ : IsAbsoluteFiberwiseBasis sq n ξ) :
    ∀ q : ℤ, IsIso (overBaseCohomologyMap sq n ξ q) := sorry

end AlgebraicGeometry.Scheme.DeRham.LerayHirsch
