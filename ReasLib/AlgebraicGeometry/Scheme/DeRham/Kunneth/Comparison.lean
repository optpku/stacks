/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Kunneth.Complex
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.Map
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.Wedge
public import ReasLib.AlgebraicGeometry.Scheme.Module.DifferentialOperator.Derived.ExternalProduct
public import ReasLib.Algebra.Homology.Embedding.Bifunctor

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape
open AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme.Hom
open CategoryTheory.MonoidalCategory SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.DeRham.Kunneth

/-- The objectwise map on relative form presentations induced by a square of ring presheaves. -/
noncomputable def presheafFormMapComponent
    {C : Type u} [Category.{v} C]
    {O₁ O₂ O₁' O₂' : Cᵒᵖ ⥤ CommRingCat.{max u v}}
    {a : O₁ ⟶ O₁'} {φ : O₁ ⟶ O₂} {φ' : O₁' ⟶ O₂'} {b : O₂ ⟶ O₂'}
    (sq : CommSq a φ φ' b) (p : ℕ) (U : Cᵒᵖ) :
    (PresheafOfModules.DeRham.form φ p).obj U ⟶
      ((PresheafOfModules.DeRham.restriction b).obj
        (PresheafOfModules.DeRham.form φ' p)).obj U :=
  CommRingCat.DeRham.formMapApp
    (PresheafOfModules.DeRham.square_app sq U) p

/-- The objectwise maps on relative form presentations commute with restriction maps. -/
theorem presheafFormMapComponent_naturality
    {C : Type u} [Category.{v} C]
    {O₁ O₂ O₁' O₂' : Cᵒᵖ ⥤ CommRingCat.{max u v}}
    {a : O₁ ⟶ O₁'} {φ : O₁ ⟶ O₂} {φ' : O₁' ⟶ O₂'} {b : O₂ ⟶ O₂'}
    (sq : CommSq a φ φ' b) (p : ℕ) {U V : Cᵒᵖ} (i : U ⟶ V) :
    (PresheafOfModules.DeRham.form φ p).map i ≫
        (ModuleCat.restrictScalars ((CategoryTheory.Presheaf.ringPresheafOfComm O₂).map i).hom).map
          (presheafFormMapComponent sq p V) =
      presheafFormMapComponent sq p U ≫
        ((PresheafOfModules.DeRham.restriction b).obj
          (PresheafOfModules.DeRham.form φ' p)).map i := sorry

/-- The morphism of relative form presheaves induced by a square of ring presheaves. -/
noncomputable def presheafFormMap
    {C : Type u} [Category.{v} C]
    {O₁ O₂ O₁' O₂' : Cᵒᵖ ⥤ CommRingCat.{max u v}}
    {a : O₁ ⟶ O₁'} {φ : O₁ ⟶ O₂} {φ' : O₁' ⟶ O₂'} {b : O₂ ⟶ O₂'}
    (sq : CommSq a φ φ' b) (p : ℕ) :
    PresheafOfModules.DeRham.form φ p ⟶
      (PresheafOfModules.DeRham.restriction b).obj
        (PresheafOfModules.DeRham.form φ' p) where
  app U := presheafFormMapComponent sq p U
  naturality i := presheafFormMapComponent_naturality sq p i

/-- Sheafification of the canonical map on relative form presentations. -/
noncomputable def sheafFormMap
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat.{max u v}}
    {a : O₁ ⟶ O₁'} {φ : O₁ ⟶ O₂} {φ' : O₁' ⟶ O₂'} {b : O₂ ⟶ O₂'}
    (sq : CommSq a φ φ' b) (p : ℕ) :
    SheafOfModules.RingedSite.DeRham.form φ p ⟶
      (SheafOfModules.RingedSite.DeRham.restriction b).obj
        (SheafOfModules.RingedSite.DeRham.form φ' p) :=
  (moduleSheafification O₂).map
      (presheafFormMap
        (SheafOfModules.RingedSite.DeRham.square_hom sq) p) ≫
    (ModuleSheafification.restrictionComponentIso b
      (PresheafOfModules.DeRham.form φ'.hom p)).hom

/-- The sectionwise map from forms of direct-image rings to the direct image of forms. -/
noncomputable def directImageFormComponent
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    {O₁ O₂ : X.Sheaf CommRingCat.{u}} (φ : O₁ ⟶ O₂)
    (p : ℕ) (U : (TopologicalSpace.Opens Y)ᵒᵖ) :
    (PresheafOfModules.DeRham.form
      (TopCat.Sheaf.DeRham.DirectImage.ringMap f φ).hom p).obj U ⟶
      (((TopCat.Sheaf.DeRham.DirectImage.modules f O₂).obj
        (TopCat.Sheaf.DeRham.form φ p)).val).obj U :=
  ((moduleSheafificationUnit O₂).app
    (PresheafOfModules.DeRham.form φ.hom p)).app
      ((TopologicalSpace.Opens.map f).op.obj U)

/-- The sectionwise direct-image maps on forms commute with restriction maps. -/
theorem directImageFormComponent_naturality
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    {O₁ O₂ : X.Sheaf CommRingCat.{u}} (φ : O₁ ⟶ O₂)
    (p : ℕ) {U V : (TopologicalSpace.Opens Y)ᵒᵖ} (i : U ⟶ V) :
    (PresheafOfModules.DeRham.form
        (TopCat.Sheaf.DeRham.DirectImage.ringMap f φ).hom p).map i ≫
      (ModuleCat.restrictScalars
        (((TopCat.Sheaf.DeRham.DirectImage.ring f O₂).presheaf.map i).hom)).map
        (directImageFormComponent f φ p V) =
      directImageFormComponent f φ p U ≫
        (((TopCat.Sheaf.DeRham.DirectImage.modules f O₂).obj
          (TopCat.Sheaf.DeRham.form φ p)).val).map i := sorry

/-- The presheaf map from forms of direct-image rings to the direct image of forms. -/
noncomputable def directImageFormPresheaf
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    {O₁ O₂ : X.Sheaf CommRingCat.{u}} (φ : O₁ ⟶ O₂) (p : ℕ) :
    PresheafOfModules.DeRham.form
        (TopCat.Sheaf.DeRham.DirectImage.ringMap f φ).hom p ⟶
      ((TopCat.Sheaf.DeRham.DirectImage.modules f O₂).obj
        (TopCat.Sheaf.DeRham.form φ p)).val where
  app U := directImageFormComponent f φ p U
  naturality i := directImageFormComponent_naturality f φ p i

/-- The canonical map from forms of direct-image rings to the direct image of forms. -/
noncomputable def directImageFormMap
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    {O₁ O₂ : X.Sheaf CommRingCat.{u}} (φ : O₁ ⟶ O₂) (p : ℕ) :
    TopCat.Sheaf.DeRham.form
        (TopCat.Sheaf.DeRham.DirectImage.ringMap f φ) p ⟶
      (TopCat.Sheaf.DeRham.DirectImage.modules f O₂).obj
        (TopCat.Sheaf.DeRham.form φ p) :=
  ((moduleSheafificationAdjunction
    (TopCat.Sheaf.DeRham.DirectImage.ring f O₂)).homEquiv _ _).symm
      (directImageFormPresheaf f φ p ≫
        (valRestrictionIso (TopCat.Sheaf.DeRham.DirectImage.ring f O₂)
          ((TopCat.Sheaf.DeRham.DirectImage.modules f O₂).obj
            (TopCat.Sheaf.DeRham.form φ p))).hom)

/-- Direct image followed by restriction along the structure-sheaf map. -/
noncomputable abbrev stagedFormPushforward
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) : X.Modules ⥤ Y.Modules :=
  TopCat.Sheaf.DeRham.DirectImage.modules f.hom.base X.sheaf ⋙
    restrictionAlong (J := Opens.grothendieckTopology Y)
      (RingedSpace.Hom.commRingSheafPushforwardMap f)

/-- The staged direct image of modules agrees with the ringed-space direct image. -/
noncomputable def stagedFormPushforwardIso
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    stagedFormPushforward f ≅ RingedSpace.Hom.pushforward f :=
  SheafOfModules.pushforwardRestrictIso
    (TopCat.Sheaf.ringSheafOfCommMap
      (RingedSpace.Hom.commRingSheafPushforwardMap f))
    (TopCat.Sheaf.commRingSheafPushforwardId f.hom.base X.sheaf)

/-- A square of ringed spaces induces the canonical map from source forms to the direct image
of target forms. -/
noncomputable def ringedSpaceFormMap
    {X' X S' S : RingedSpace.{u}} {f : X' ⟶ X}
    {h' : X' ⟶ S'} {h : X ⟶ S} {g : S' ⟶ S}
    (sq : CommSq f h' h g) (p : ℕ) :
    RingedSpace.DeRham.form h p ⟶
      (RingedSpace.Hom.pushforward f).obj (RingedSpace.DeRham.form h' p) :=
  sheafFormMap (RingedSpace.DeRham.structureSquare sq) p ≫
    (restrictionAlong (J := Opens.grothendieckTopology X)
      (RingedSpace.Hom.commRingSheafPushforwardMap f)).map
        (directImageFormMap f.hom.base (RingedSpace.DeRham.structureMap h') p) ≫
    (stagedFormPushforwardIso f).hom.app (RingedSpace.DeRham.form h' p)

/-- The tautological square from a composite ringed-space morphism to its first factor. -/
theorem compositionSquare
    {X' X S : RingedSpace.{u}} (f : X' ⟶ X) (h : X ⟶ S) :
    CommSq f (f ≫ h) h (𝟙 S) := sorry

/-- Pullback of a relative form maps canonically to the corresponding form of the composite. -/
noncomputable def pullbackFormComparison
    {X' X S : RingedSpace.{u}} (f : X' ⟶ X) (h : X ⟶ S) (p : ℕ) :
    (RingedSpace.Hom.pullback f).obj (RingedSpace.DeRham.form h p) ⟶
      RingedSpace.DeRham.form (f ≫ h) p :=
  ((RingedSpace.Hom.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (ringedSpaceFormMap (compositionSquare f h) p)

variable {S X Y : Scheme.{u}}

/-- Pullback along the first projection sends relative forms canonically to relative forms on
the fiber product. -/
noncomputable def fstFormComparison (a : X ⟶ S) (b : Y ⟶ S) (p : ℕ) :
    (RingedSpace.Hom.pullback (pullback.fst a b).toLRSHom.toShHom).obj
        (RingedSpace.DeRham.form a.toLRSHom.toShHom p) ⟶
      RingedSpace.DeRham.form (pullback.fst a b ≫ a).toLRSHom.toShHom p :=
  pullbackFormComparison (pullback.fst a b).toLRSHom.toShHom a.toLRSHom.toShHom p

/-- The two structure morphisms from the fiber product to the base agree. -/
theorem fiberStructureMap_eq (a : X ⟶ S) (b : Y ⟶ S) :
    (pullback.snd a b ≫ b).toLRSHom.toShHom =
      (pullback.fst a b ≫ a).toLRSHom.toShHom := sorry

/-- Transport relative forms between the two equal structure maps on the fiber product. -/
noncomputable def fiberFormTransport (a : X ⟶ S) (b : Y ⟶ S) (q : ℕ) :
    RingedSpace.DeRham.form (pullback.snd a b ≫ b).toLRSHom.toShHom q ⟶
      RingedSpace.DeRham.form (pullback.fst a b ≫ a).toLRSHom.toShHom q :=
  eqToHom (congrArg (fun f ↦ RingedSpace.DeRham.form f q) (fiberStructureMap_eq a b))

/-- Pullback along the second projection, followed by the fiber-product identification, sends
relative forms canonically to relative forms for the chosen structure map. -/
noncomputable def sndFormComparison (a : X ⟶ S) (b : Y ⟶ S) (q : ℕ) :
    (RingedSpace.Hom.pullback (pullback.snd a b).toLRSHom.toShHom).obj
        (RingedSpace.DeRham.form b.toLRSHom.toShHom q) ⟶
      RingedSpace.DeRham.form (pullback.fst a b ≫ a).toLRSHom.toShHom q :=
  pullbackFormComparison (pullback.snd a b).toLRSHom.toShHom b.toLRSHom.toShHom q ≫
    fiberFormTransport a b q

/-- The tensor of the two pullback comparisons, before applying the wedge product. -/
noncomputable def externalFormTensorComparison
    (a : X ⟶ S) (b : Y ⟶ S) (p q : ℕ) :
    Scheme.Modules.externalTensorProduct a b
        (RingedSpace.DeRham.form a.toLRSHom.toShHom p)
        (RingedSpace.DeRham.form b.toLRSHom.toShHom q) ⟶
      (RingedSpace.DeRham.form (pullback.fst a b ≫ a).toLRSHom.toShHom p ⊗
        RingedSpace.DeRham.form (pullback.fst a b ≫ a).toLRSHom.toShHom q) :=
  fstFormComparison a b p ⊗ₘ sndFormComparison a b q

/-- Wedge multiplication for relative forms on the fiber product. -/
noncomputable def fiberFormWedge (a : X ⟶ S) (b : Y ⟶ S) (p q : ℕ) :
    (RingedSpace.DeRham.form (pullback.fst a b ≫ a).toLRSHom.toShHom p ⊗
      RingedSpace.DeRham.form (pullback.fst a b ≫ a).toLRSHom.toShHom q) ⟶
        RingedSpace.DeRham.form (pullback.fst a b ≫ a).toLRSHom.toShHom (p + q) :=
  SheafOfModules.RingedSite.DeRham.formWedge
    (RingedSpace.DeRham.structureMap (pullback.fst a b ≫ a).toLRSHom.toShHom) p q

/-- The canonical bidegree map from the external tensor product of two relative-form sheaves
to the relative forms on their fiber product. -/
noncomputable def externalFormComparison (a : X ⟶ S) (b : Y ⟶ S) (p q : ℕ) :
    Scheme.Modules.externalTensorProduct a b
        (RingedSpace.DeRham.form a.toLRSHom.toShHom p)
        (RingedSpace.DeRham.form b.toLRSHom.toShHom q) ⟶
      RingedSpace.DeRham.form (pullback.fst a b ≫ a).toLRSHom.toShHom (p + q) :=
  externalFormTensorComparison a b p q ≫ fiberFormWedge a b p q

/-- The bidegree exterior-form comparison transported to the coefficient modules underlying
the chosen external-product functor. -/
noncomputable def externalFormOperatorHom (a : X ⟶ S) (b : Y ⟶ S)
    (T : FiniteOrderDifferentialOperatorCat a ⥤
      FiniteOrderDifferentialOperatorCat b ⥤
        FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
    (hT : IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
    (i j : ℕ) :
    (restrictionAlong
      (FiniteOrderDifferentialOperatorCat.coefficientMap (pullback.fst a b ≫ a))).obj
        (FiniteOrderDifferentialOperatorCat.underlying
          (pullback.fst a b ≫ a) ((T.obj (operatorForm a i)).obj (operatorForm b j))) ⟶
      (restrictionAlong
        (FiniteOrderDifferentialOperatorCat.coefficientMap (pullback.fst a b ≫ a))).obj
        (FiniteOrderDifferentialOperatorCat.underlying
          (pullback.fst a b ≫ a) (operatorForm (pullback.fst a b ≫ a) (i + j))) :=
  (restrictionAlong
    (FiniteOrderDifferentialOperatorCat.coefficientMap (pullback.fst a b ≫ a))).map
      (eqToHom (hT.obj_eq (operatorForm a i) (operatorForm b j)) ≫
        eqToHom (congrArg₂ (Scheme.Modules.externalTensorProduct a b)
          (FiniteOrderDifferentialOperatorCat.underlying_ofQCoh a (formQCoh a i))
          (FiniteOrderDifferentialOperatorCat.underlying_ofQCoh b (formQCoh b j))) ≫
        externalFormComparison a b i j ≫
        eqToHom (FiniteOrderDifferentialOperatorCat.underlying_ofQCoh
          (pullback.fst a b ≫ a) (formQCoh (pullback.fst a b ≫ a) (i + j))).symm)

/-- The transported bidegree exterior-form comparison has differential-operator order zero. -/
theorem externalFormOperatorHom_isOrderZero (a : X ⟶ S) (b : Y ⟶ S)
    (T : FiniteOrderDifferentialOperatorCat a ⥤
      FiniteOrderDifferentialOperatorCat b ⥤
        FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
    (hT : IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
    (i j : ℕ) :
    IsDifferentialOperatorOfOrder.{u, u, u, u}
      (FiniteOrderDifferentialOperatorCat.coefficientMap (pullback.fst a b ≫ a))
      (externalFormOperatorHom a b T hT i j) 0 := sorry

/-- The canonical bidegree comparison bundled as an order-zero differential operator. -/
noncomputable def externalFormOperator (a : X ⟶ S) (b : Y ⟶ S)
    (T : FiniteOrderDifferentialOperatorCat a ⥤
      FiniteOrderDifferentialOperatorCat b ⥤
        FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
    (hT : IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
    (i j : ℕ) :
    (T.obj (operatorForm a i)).obj (operatorForm b j) ⟶
      operatorForm (pullback.fst a b ≫ a) (i + j) :=
  ⟨externalFormOperatorHom a b T hT i j, 0,
    externalFormOperatorHom_isOrderZero a b T hT i j⟩

section Comparison

variable (a : X ⟶ S) (b : Y ⟶ S)
variable (T : FiniteOrderDifferentialOperatorCat a ⥤
  FiniteOrderDifferentialOperatorCat b ⥤
    FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
variable (hT : IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
variable [T.PreservesZeroMorphisms] [∀ M, (T.obj M).PreservesZeroMorphisms]
variable [HomologicalComplex.HasMapBifunctor (operatorComplex a) (operatorComplex b) T (up ℕ)]
variable [HomologicalComplex.HasMapBifunctor
  (extendedOperatorComplex a) (extendedOperatorComplex b) T (up ℤ)]

/-- The degreewise map from the total external product of the two nonnegative operator de Rham
complexes to the operator de Rham complex of the fiber product. -/
noncomputable def comparisonComponent (n : ℕ) :
    (HomologicalComplex.mapBifunctor (operatorComplex a) (operatorComplex b) T (up ℕ)).X n ⟶
      (operatorComplex (pullback.fst a b ≫ a)).X n :=
  HomologicalComplex.mapBifunctorDesc fun i j hij ↦
    externalFormOperator a b T hT i j ≫
      eqToHom (congrArg (operatorComplex (pullback.fst a b ≫ a)).X hij)

/-- The degreewise comparisons commute with the total and de Rham differentials. -/
theorem comparisonComponent_comm (i j : ℕ) (hij : (up ℕ).Rel i j) :
    comparisonComponent a b T hT i ≫
        (operatorComplex (pullback.fst a b ≫ a)).d i j =
      (HomologicalComplex.mapBifunctor
        (operatorComplex a) (operatorComplex b) T (up ℕ)).d i j ≫
        comparisonComponent a b T hT j := sorry

/-- Every degreewise exterior-form comparison is an isomorphism. -/
theorem comparisonComponent_isIso (n : ℕ) :
    IsIso (comparisonComponent a b T hT n) := sorry

/-- The canonical comparison of the nonnegative operator de Rham complexes. -/
noncomputable def operatorComparisonNat :
    HomologicalComplex.mapBifunctor (operatorComplex a) (operatorComplex b) T (up ℕ) ⟶
      operatorComplex (pullback.fst a b ≫ a) :=
  HomologicalComplex.Hom.mk (comparisonComponent a b T hT)
    (comparisonComponent_comm a b T hT)

/-- The canonical map from the extended operator external-product total to the extended
operator de Rham complex of the fiber product. -/
noncomputable def operatorComparison :
    Modules.Kunneth.externalTotalComplex a b T hT
        (extendedOperatorComplex a) (extendedOperatorComplex b) ⟶
      extendedOperatorComplex (pullback.fst a b ≫ a) :=
  embeddingUpNat.extendBifunctorHom T (operatorComplex a) (operatorComplex b) ≫
    HomologicalComplex.extendMap (operatorComparisonNat a b T hT) embeddingUpNat

/-- The standard coefficient-module realization of
`Tot(Ωᵈᴿ[X/S] ⊠ Ωᵈᴿ[Y/S])`. -/
noncomputable abbrev externalDeRhamTotal :=
  (FiniteOrderDifferentialOperatorCat.toCoefficientComplex
    (pullback.fst a b ≫ a)).obj
      (Modules.Kunneth.externalTotalComplex a b T hT
        (extendedOperatorComplex a) (extendedOperatorComplex b))

/-- The canonical coefficient-complex map from the total external product to the standard
relative de Rham complex of the fiber product. -/
noncomputable def comparison :
    externalDeRhamTotal a b T hT ⟶
      (RingedSpace.DeRham.complex
        (pullback.fst a b ≫ a).toLRSHom.toShHom).extend embeddingUpNat :=
  (FiniteOrderDifferentialOperatorCat.toCoefficientComplex
      (pullback.fst a b ≫ a)).map (operatorComparison a b T hT) ≫
    (operatorDeRhamIso (pullback.fst a b ≫ a)).hom

/-- The degree-`n` component of `comparison` is coefficient realization of the operator
comparison followed by the standard de Rham bridge. -/
theorem comparison_f (n : ℤ) :
    (comparison a b T hT).f n =
      ((FiniteOrderDifferentialOperatorCat.toCoefficientComplex
        (pullback.fst a b ≫ a)).map (operatorComparison a b T hT)).f n ≫
        (operatorDeRhamIso (pullback.fst a b ≫ a)).hom.f n := sorry

/-- The bundled isomorphism underlying the canonical de Rham Kunneth comparison. -/
noncomputable def comparisonIso [IsIso (comparison a b T hT)] :
    externalDeRhamTotal a b T hT ≅
      (RingedSpace.DeRham.complex
        (pullback.fst a b ≫ a).toLRSHom.toShHom).extend embeddingUpNat :=
  asIso (comparison a b T hT)

/-- The forward map of `comparisonIso` is the canonical comparison. -/
theorem comparisonIso_hom [IsIso (comparison a b T hT)] :
    (comparisonIso a b T hT).hom = comparison a b T hT := sorry

/-- The canonical de Rham Kunneth comparison is an isomorphism. -/
theorem comparison_isIso : IsIso (comparison a b T hT) := sorry

end Comparison

end AlgebraicGeometry.Scheme.DeRham.Kunneth
