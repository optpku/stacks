module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Lift.Relative
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Thickening.Flat

/-!
# Relative Hom-action on lifts of module maps

Along a strict morphism of first-order thickenings, if `𝒢'` is flat over `S'`,
`Hom_{𝒪_X}(ℱ, 𝒢 ⊗_{𝒪_X} f^* 𝒥)` acts on `𝒪_{X'}`-linear lifts of `φ : ℱ ⟶ 𝒢` by
postcomposition with the comparison `𝒢 ⊗ f^* 𝒥 ⟶ ℐ𝒢'`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Hom.ModuleMap
open AlgebraicGeometry.RingedSpace.Hom.ModuleMap.Lift
open scoped AlgebraicGeometry

noncomputable section

universe u

open AlgebraicGeometry.RingedSpace.Thickening.Hom
open AlgebraicGeometry.RingedSpace.Thickening.Hom.ModuleMap

#check (AlgebraicGeometry.RingedSpace.Thickening.Hom.ModuleMap.sourceIdealTensorCompare :
  {T U : Thickening.{u}} → [IsFirstOrderThickening T.hom] →
    [IsFirstOrderThickening U.hom] → (g : T ⟶ U) → (G' : T.right.Modules) →
    (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom) ⟶
      idealMulRestrict T.hom G')

#check (AlgebraicGeometry.RingedSpace.Thickening.Hom.ModuleMap.sourceIdealTensorCompare_comp :
  ∀ {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
    (g : T ⟶ U) (G' : T.right.Modules),
    sourceIdealTensorCompare g G' =
      (β_ ((T.hom^*).obj G') ((g.left^*).obj (idealModule U.hom))).hom ≫
        sourceIdealMulMap g G')

#check (AlgebraicGeometry.RingedSpace.Thickening.Hom.ModuleMap.relativePerturb :
  {T U : Thickening.{u}} → [IsFirstOrderThickening T.hom] →
    [IsFirstOrderThickening U.hom] → (g : T ⟶ U) → {F' G' : T.right.Modules} →
    {φ : (T.hom^*).obj F' ⟶ (T.hom^*).obj G'} →
    ((T.hom^*).obj F' ⟶ (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom)) →
    Lift F' G' φ → Lift F' G' φ)

#check (AlgebraicGeometry.RingedSpace.Thickening.Hom.ModuleMap.relativePerturb_hom :
  ∀ {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
    (g : T ⟶ U) {F' G' : T.right.Modules}
    {φ : (T.hom^*).obj F' ⟶ (T.hom^*).obj G'}
    (α : (T.hom^*).obj F' ⟶
      (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom))
    (φ' : Lift F' G' φ),
    (relativePerturb g α φ').hom =
      (perturb (α ≫ sourceIdealTensorCompare g G') φ').hom)

#check (AlgebraicGeometry.RingedSpace.Thickening.Hom.ModuleMap.relativePerturb_zero :
  ∀ {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
    (g : T ⟶ U) {F' G' : T.right.Modules}
    {φ : (T.hom^*).obj F' ⟶ (T.hom^*).obj G'} (φ' : Lift F' G' φ),
    relativePerturb g 0 φ' = φ')

#check (AlgebraicGeometry.RingedSpace.Thickening.Hom.ModuleMap.relativePerturb_add :
  ∀ {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
    (g : T ⟶ U) {F' G' : T.right.Modules}
    {φ : (T.hom^*).obj F' ⟶ (T.hom^*).obj G'}
    (α β : (T.hom^*).obj F' ⟶
      (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom)) (φ' : Lift F' G' φ),
    relativePerturb g (α + β) φ' = relativePerturb g α (relativePerturb g β φ'))

#check (AlgebraicGeometry.RingedSpace.Thickening.Hom.isIso_sourceIdealMulMap_of_isFlatOver :
  ∀ {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
    (g : T ⟶ U) {G' : T.right.Modules} [SheafOfModules.IsFlatOver G' g.right],
    IsStrict g → IsIso (sourceIdealMulMap g G'))

#check (AlgebraicGeometry.RingedSpace.Thickening.Hom.ModuleMap.homSourceIdealMulEquiv :
  {T U : Thickening.{u}} → [IsFirstOrderThickening T.hom] →
    [IsFirstOrderThickening U.hom] → (g : T ⟶ U) → {G' : T.right.Modules} →
    [IsIso (sourceIdealMulMap g G')] → (F' : T.right.Modules) →
    ((T.hom^*).obj F' ⟶
      (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom)) ≃
      ((T.hom^*).obj F' ⟶ idealMulRestrict T.hom G'))

#check (AlgebraicGeometry.RingedSpace.Thickening.Hom.ModuleMap.homSourceIdealMulEquiv_apply :
  ∀ {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
    (g : T ⟶ U) {G' : T.right.Modules} [IsIso (sourceIdealMulMap g G')]
    {F' : T.right.Modules}
    (α : (T.hom^*).obj F' ⟶
      (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom)),
    homSourceIdealMulEquiv g F' α = α ≫ sourceIdealTensorCompare g G')

#check (AlgebraicGeometry.RingedSpace.Thickening.Hom.ModuleMap.relativePerturbEquiv :
  {T U : Thickening.{u}} → [IsFirstOrderThickening T.hom] →
    [IsFirstOrderThickening U.hom] → (g : T ⟶ U) → {F' G' : T.right.Modules} →
    {φ : (T.hom^*).obj F' ⟶ (T.hom^*).obj G'} →
    [IsIso (sourceIdealMulMap g G')] → (φ' : Lift F' G' φ) →
    ((T.hom^*).obj F' ⟶
      (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom)) ≃
      Lift F' G' φ)

#check (AlgebraicGeometry.RingedSpace.Thickening.Hom.ModuleMap.relativePerturbEquiv_apply :
  ∀ {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
    (g : T ⟶ U) {F' G' : T.right.Modules}
    {φ : (T.hom^*).obj F' ⟶ (T.hom^*).obj G'} [IsIso (sourceIdealMulMap g G')]
    (φ' : Lift F' G' φ)
    (α : (T.hom^*).obj F' ⟶
      (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom)),
    relativePerturbEquiv g φ' α = relativePerturb g α φ')
