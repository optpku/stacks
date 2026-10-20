module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.LowerShriek

/-!
# Alternating-face complex of `g_{n!} O_n` on a morphism diagram of sites

The simplicial sheaf of `O`-modules `n ↦ g_{n!} O_n`
on the total site, its augmentation to the rank-one sheaf `O`, and the associated
alternating-face chain complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex RingedSite
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable [UnivLE.{max u v, w}]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [(topology C J).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The rank-one sheaf of modules `O_n` on the degree-`n` site. -/
abbrev componentUnit (n : SimplexCategory) :
    SheafOfModules.{w} (componentRingSheaf C J O n) :=
  SheafOfModules.unit (componentRingSheaf C J O n)

/-- The comparison `f_φ^* O_n ⟶ O_m` of rank-one modules along a simplex operator. -/
def facePullback_unit_counit {n m : SimplexCategory} (φ : n ⟶ m) :
    (ringedToposMap_pullback C J O φ).obj (componentUnit C J O n) ⟶
      componentUnit C J O m :=
  SheafOfModules.pullbackObjUnitToUnit (ringedToposMapDirectStructure C J O φ)

/-- The comparison `f_φ^* O_n ⟶ O_m` is an isomorphism. -/
instance facePullback_unit_counit_isIso {n m : SimplexCategory} (φ : n ⟶ m) :
    IsIso (facePullback_unit_counit C J O φ) :=
  sorry

/-- The comparison `O_m ⟶ f_φ^* O_n` of rank-one modules along a simplex operator. -/
def facePullback_unit {n m : SimplexCategory} (φ : n ⟶ m) :
    componentUnit C J O m ⟶
      (ringedToposMap C J O φ).modulePullback.obj (componentUnit C J O n) :=
  CategoryTheory.inv (facePullback_unit_counit C J O φ) ≫
    (ringedToposMap_pullbackIso C J O φ).hom.app (componentUnit C J O n)

/-- The comparison `O_m ⟶ f_φ^* O_n` is an isomorphism. -/
instance facePullback_unit_isIso {n m : SimplexCategory} (φ : n ⟶ m) :
    IsIso (facePullback_unit C J O φ) :=
  sorry

/-- The identity comparison `O_n ⟶ (ofStage C n)_* O` of ring sheaves, pinning
the site functor to `ofStage C n` rather than the identity on `C_n`. -/
def ofStage_identityRingMap (n : SimplexCategory) :
    componentRingSheaf C J O n ⟶
      ((ofStage C n).sheafPushforwardContinuous RingCat.{w}
        (J n).toGrothendieck (topology C J)).obj O :=
  𝟙 (componentRingSheaf C J O n)

/-- The comparison `O_n ⟶ g_n^* O` of rank-one modules along `ofStage C n`. -/
def ofStage_unit_hom (n : SimplexCategory) :
    componentUnit C J O n ⟶
      (Cocontinuous.moduleInverseImage (ofStage C n) O).obj
        (SheafOfModules.unit O) :=
  SheafOfModules.unitToPushforwardObjUnit (ofStage_identityRingMap C J O n)

/-- The adjunct of `facePullback_unit ≫ moduleLowerShriek_component` along `g_{m!} ⊣ g_m^*`. -/
def lowerShriekUnit_map {n m : SimplexCategory} (φ : n ⟶ m) :
    (moduleLowerShriek C J O m).obj (componentUnit C J O m) ⟶
      (moduleLowerShriek C J O n).obj (componentUnit C J O n) :=
  ((moduleLowerShriek.adjunction C J O m).homEquiv
      (componentUnit C J O m)
      ((moduleLowerShriek C J O n).obj (componentUnit C J O n))).symm
    (facePullback_unit C J O φ ≫
      moduleLowerShriek_component C J O φ (componentUnit C J O n) ≫
      (moduleInverseImageIsoModulePullback C J O m).inv.app
        ((moduleLowerShriek C J O n).obj (componentUnit C J O n)))

/-- Identity simplex operators induce identity structure maps of `n ↦ g_{n!} O_n`. -/
theorem lowerShriekUnit_map_id (n : SimplexCategory) :
    lowerShriekUnit_map C J O (𝟙 n) =
      𝟙 ((moduleLowerShriek C J O n).obj (componentUnit C J O n)) :=
  sorry

/-- Structure maps of `n ↦ g_{n!} O_n` are functorial in simplex operators. -/
theorem lowerShriekUnit_map_comp {l n m : SimplexCategory}
    (ψ : l ⟶ n) (φ : n ⟶ m) :
    lowerShriekUnit_map C J O (ψ ≫ φ) =
      lowerShriekUnit_map C J O φ ≫ lowerShriekUnit_map C J O ψ :=
  sorry

/-- The simplicial sheaf of `O`-modules `n ↦ g_{n!} O_n` on the total site. -/
def lowerShriekUnit : SimplicialObject (SheafOfModules.{w} O) where
  obj n := (moduleLowerShriek C J O n.unop).obj (componentUnit C J O n.unop)
  map f := lowerShriekUnit_map C J O f.unop
  map_id n := lowerShriekUnit_map_id C J O n.unop
  map_comp f g := lowerShriekUnit_map_comp C J O g.unop f.unop

/-- The value of `lowerShriekUnit` at `n` is `g_{n!} O_n`. -/
theorem lowerShriekUnit_obj (n : SimplexCategory) :
    (lowerShriekUnit C J O).obj (op n) =
      (moduleLowerShriek C J O n).obj (componentUnit C J O n) :=
  sorry

/-- The face map `d_i : g_{(n+1)!} O_{n+1} ⟶ g_{n!} O_n`. -/
def moduleFace (n : ℕ) (i : Fin (n + 2)) :
    (lowerShriekUnit C J O).obj (op ⦋n + 1⦌) ⟶
      (lowerShriekUnit C J O).obj (op ⦋n⦌) :=
  (lowerShriekUnit C J O).δ i

/-- The component of the augmentation `g_{n!} O_n ⟶ O` at a simplex `n`. -/
def moduleAugmented_hom_app (n : SimplexCategoryᵒᵖ) :
    (lowerShriekUnit C J O).obj n ⟶ SheafOfModules.unit O :=
  ((moduleLowerShriek.adjunction C J O n.unop).homEquiv
      (componentUnit C J O n.unop) (SheafOfModules.unit O)).symm
    (ofStage_unit_hom C J O n.unop)

/-- Naturality of the degreewise augmentation `g_{n!} O_n ⟶ O`. -/
theorem moduleAugmented_hom_naturality :
    ∀ ⦃n m : SimplexCategoryᵒᵖ⦄ (f : n ⟶ m),
      (lowerShriekUnit C J O).map f ≫ moduleAugmented_hom_app C J O m =
        moduleAugmented_hom_app C J O n ≫
          ((SimplicialObject.const _).obj (SheafOfModules.unit O)).map f :=
  sorry

/-- The natural transformation `n ↦ g_{n!} O_n ⟶ const O`. -/
def moduleAugmented_hom :
    lowerShriekUnit C J O ⟶
      (SimplicialObject.const _).obj (SheafOfModules.unit O) where
  app := moduleAugmented_hom_app C J O
  naturality := moduleAugmented_hom_naturality C J O

/-- The augmented simplicial object of `g_{n!} O_n` over the rank-one sheaf `O`. -/
def moduleAugmented : SimplicialObject.Augmented (SheafOfModules.{w} O) where
  left := lowerShriekUnit C J O
  right := SheafOfModules.unit O
  hom := moduleAugmented_hom C J O

/-- The alternating-face chain complex `… → g_{2!} O_2 → g_{1!} O_1 → g_{0!} O_0`. -/
abbrev moduleComplex : ChainComplex (SheafOfModules.{w} O) ℕ :=
  (alternatingFaceMapComplex _).obj
    (SimplicialObject.Augmented.drop.obj (moduleAugmented C J O))

/-- Degree `n` of `moduleComplex C J O` is the sheaf of modules `g_{n!} O_n`. -/
theorem moduleComplex_X (n : ℕ) :
    (moduleComplex C J O).X n =
      (moduleLowerShriek C J O ⦋n⦌).obj (componentUnit C J O ⦋n⦌) :=
  sorry

/-- Differentials of `moduleComplex C J O` are the alternating sums of face maps. -/
theorem moduleComplex_d_eq (n : ℕ) :
    (moduleComplex C J O).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • moduleFace C J O n i :=
  sorry

/-- The canonical chain-map augmentation from `moduleComplex C J O` to the rank-one
sheaf `O` concentrated in degree zero. -/
def moduleAugmentation :
    moduleComplex C J O ⟶
      (ChainComplex.single₀ _).obj (SheafOfModules.unit O) :=
  AlternatingFaceMapComplex.ε.app (moduleAugmented C J O)

/-- The degree-zero component of `moduleAugmentation C J O` is the simplicial
augmentation at `⦋0⦌`. -/
theorem moduleAugmentation_f_zero :
    (moduleAugmentation C J O).f 0 = (moduleAugmented C J O).hom.app (op ⦋0⦌) :=
  sorry

/-- The canonical alternating-face augmentation of the lower-shriek unit modules
is a quasi-isomorphism to the unit module concentrated in degree zero. -/
instance moduleAugmentation_quasiIso :
    QuasiIso
      (moduleAugmentation C J O :
        moduleComplex C J O ⟶
          (ChainComplex.single₀ _).obj (SheafOfModules.unit O)) :=
  sorry

end CategoryTheory.SimplicialSites
