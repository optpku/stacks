module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct
public import ReasLib.AlgebraicGeometry.GroupoidsOver.DeformationSituation.FixedObject
public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalDeformation

/-!
# Dual obstruction data at a finite-type object

An unbounded complex, a tangent comparison, and natural obstruction classes
at an affine finite-type object of a category fibred in groupoids.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {A : Type u} [CommRing A]

/-- The functor sending `M` to the `n`-th homology of the derived tensor of `M`
with `K`. -/
def homologyTensor (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  ModuleCat.single0Functor ⋙
    DerivedCategory.derivedTensorProduct (DerivedCategory.Q.obj K) ⋙
    DerivedCategory.homologyFunctor (ModuleCat A) n

/-- The value of `homologyTensor K n` on `M` is the `n`-th homology of the
derived tensor of `K` with `M` in degree zero. -/
theorem homologyTensor_obj (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (M : ModuleCat.{u} A) :
    (homologyTensor K n).obj M =
      (DerivedCategory.homologyFunctor (ModuleCat A) n).obj
        ((DerivedCategory.derivedTensorProduct (DerivedCategory.Q.obj K)).obj
          (ModuleCat.single0 M)) :=
  sorry

/-- Symmetry identifies the homology of the derived tensor product with the
homology obtained by interchanging its factors. -/
def homologyTensor_comm (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (M : ModuleCat.{u} A) :
    (homologyTensor K n).obj M ≅
      (DerivedCategory.homologyFunctor (ModuleCat A) n).obj
        ((DerivedCategory.derivedTensorProduct (ModuleCat.single0 M)).obj
          (DerivedCategory.Q.obj K)) :=
  (DerivedCategory.homologyFunctor (ModuleCat A) n).mapIso
    (DerivedCategory.derivedTensorProduct_comm (DerivedCategory.Q.obj K)
      (ModuleCat.single0 M)).symm

/-- Universe lift of `homologyTensor K n` to `ModuleCat.{u+1}`, matching the
landing universe of `tangentFunctor`. -/
def homologyTensorUlift (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    ModuleCat.{u} A ⥤ ModuleCat.{u + 1} A :=
  homologyTensor K n ⋙ ModuleCat.uliftFunctor.{u + 1, u} A

variable {S : Scheme.{u}} [IsLocallyNoetherian S]

/-- Dual obstruction data at an affine finite-type object consists of an
arbitrary complex, a natural isomorphism from the tangent functor to its
first derived tensor homology, and natural second-homology obstruction
classes vanishing exactly when a lift exists. -/
structure DualObstruction (X : GroupoidsOver S) [HasStrongRimSchlessinger X] where
  /-- The coordinate ring of an affine open in the base scheme. -/
  base : CommRingCat.{u}
  /-- The coefficient algebra of the affine object. -/
  coefficientAlgebra : CommAlgCat.{u} base
  /-- The open subset of the base covered by the affine chart. -/
  affineOpen : S.Opens
  /-- An affine chart on the chosen open subset. -/
  chart : Spec base ≅ affineOpen.toScheme
  /-- The total-category object over the coefficient spectrum. -/
  obj : X.total
  /-- The stored object lies over the structure map determined by the chart. -/
  over_obj : X.p.obj obj = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap base coefficientAlgebra)) ≫
        (chart.hom ≫ affineOpen.ι))
  /-- The structure morphism is locally of finite type. -/
  locallyOfFiniteType : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap base coefficientAlgebra)) ≫
        (chart.hom ≫ affineOpen.ι))
  /-- The structure morphism is quasi-compact. -/
  quasiCompact : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap base coefficientAlgebra)) ≫
        (chart.hom ≫ affineOpen.ι))
  /-- The complex over the coefficient ring. -/
  complex : CochainComplex (ModuleCat.{u} coefficientAlgebra) ℤ
  /-- The tangent functor is the first derived tensor homology, with the canonical universe lift. -/
  tangentIso : tangentFunctor (Functor.Fiber.mk over_obj) ≅ homologyTensorUlift complex 1
  /-- The obstruction class of each deformation situation over the fixed object. -/
  obstruction :
    let ξ : ObjectOverSpec X := {
      toCommRingCat := CommRingCat.of coefficientAlgebra
      toS := Spec.map (CommRingCat.ofHom (algebraMap base coefficientAlgebra)) ≫
        (chart.hom ≫ affineOpen.ι)
      mapsIntoAffineOpen := ⟨Spec base, inferInstance, chart.hom ≫ affineOpen.ι,
        inferInstance, Spec.map (CommRingCat.ofHom (algebraMap base coefficientAlgebra)), rfl⟩
      obj := obj
      over_obj := over_obj }
    {σ : DeformationSituation X} → (hσ : σ.IsOver ξ) →
      (homologyTensor complex 2).obj (DeformationSituation.kernelOver hσ)
  /-- Obstruction classes are natural along every morphism fixing the coefficient ring. -/
  map_obstruction :
    let ξ : ObjectOverSpec X := {
      toCommRingCat := CommRingCat.of coefficientAlgebra
      toS := Spec.map (CommRingCat.ofHom (algebraMap base coefficientAlgebra)) ≫
        (chart.hom ≫ affineOpen.ι)
      mapsIntoAffineOpen := ⟨Spec base, inferInstance, chart.hom ≫ affineOpen.ι,
        inferInstance, Spec.map (CommRingCat.ofHom (algebraMap base coefficientAlgebra)), rfl⟩
      obj := obj
      over_obj := over_obj }
    ∀ {σ τ : DeformationSituation X}
      (hσ : σ.IsOver ξ) (hτ : τ.IsOver ξ)
      (f : DeformationSituation.Hom σ τ)
      (hf : f.toRingHom = DeformationSituation.ringHomIdOver hσ hτ),
      (homologyTensor complex 2).map
          (DeformationSituation.kernelMapOver hσ hτ f hf) (obstruction hσ) =
        obstruction hτ
  /-- A lift exists exactly when the obstruction vanishes. -/
  lifts_iff :
    let ξ : ObjectOverSpec X := {
      toCommRingCat := CommRingCat.of coefficientAlgebra
      toS := Spec.map (CommRingCat.ofHom (algebraMap base coefficientAlgebra)) ≫
        (chart.hom ≫ affineOpen.ι)
      mapsIntoAffineOpen := ⟨Spec base, inferInstance, chart.hom ≫ affineOpen.ι,
        inferInstance, Spec.map (CommRingCat.ofHom (algebraMap base coefficientAlgebra)), rfl⟩
      obj := obj
      over_obj := over_obj }
    ∀ {σ : DeformationSituation X} (hσ : σ.IsOver ξ),
      Nonempty (DeformationSituation.ObjectLift σ) ↔ obstruction hσ = 0

variable {X : GroupoidsOver S} [HasStrongRimSchlessinger X]

namespace DualObstruction

/-- The coefficient carrier of the affine object. -/
abbrev carrier (𝒟 : DualObstruction X) : Type u := 𝒟.coefficientAlgebra

/-- The commutative ring structure of the coefficient algebra. -/
abbrev commRing (𝒟 : DualObstruction X) : CommRing 𝒟.carrier :=
  𝒟.coefficientAlgebra.commRing

/-- The commutative ring structure of the affine chart's coordinate ring. -/
abbrev baseCommRing (𝒟 : DualObstruction X) : CommRing 𝒟.base := 𝒟.base.commRing

/-- The algebra structure of the affine coefficient ring over the chart ring. -/
abbrev algebra (𝒟 : DualObstruction X) : Algebra 𝒟.base 𝒟.carrier :=
  𝒟.coefficientAlgebra.algebra

/-- The open immersion obtained by composing the affine chart with the open inclusion. -/
abbrev openImmersion (𝒟 : DualObstruction X) : Spec 𝒟.base ⟶ S :=
  𝒟.chart.hom ≫ 𝒟.affineOpen.ι

/-- The structure morphism of the affine coefficient spectrum. -/
abbrev toS (𝒟 : DualObstruction X) : Spec (CommRingCat.of 𝒟.carrier) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap 𝒟.base 𝒟.carrier)) ≫ 𝒟.openImmersion

/-- The structure morphism factors through the specified affine open chart. -/
theorem factor (𝒟 : DualObstruction X) :
    Spec.map (CommRingCat.ofHom (algebraMap 𝒟.base 𝒟.carrier)) ≫
      𝒟.openImmersion = 𝒟.toS := rfl

/-- The object over the coefficient spectrum, with its chart-induced structure morphism. -/
abbrev toObjectOverSpec (𝒟 : DualObstruction X) : ObjectOverSpec X where
  toCommRingCat := CommRingCat.of 𝒟.carrier
  toS := 𝒟.toS
  mapsIntoAffineOpen := ⟨Spec 𝒟.base, inferInstance, 𝒟.openImmersion, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap 𝒟.base 𝒟.carrier)), rfl⟩
  obj := 𝒟.obj
  over_obj := 𝒟.over_obj

/-- Dual obstruction data specifies finite type, an affine-open factorization,
a tangent isomorphism, natural obstruction classes, and the lifting criterion. -/
theorem spec (𝒟 : DualObstruction X) :
    LocallyOfFiniteType 𝒟.toS ∧ QuasiCompact 𝒟.toS ∧
      (Spec.map (CommRingCat.ofHom (algebraMap 𝒟.base 𝒟.carrier)) ≫
          𝒟.openImmersion = 𝒟.toS) ∧
      IsIso 𝒟.tangentIso.hom ∧
      (∀ {σ τ : DeformationSituation X}
          (hσ : σ.IsOver 𝒟.toObjectOverSpec) (hτ : τ.IsOver 𝒟.toObjectOverSpec)
          (f : DeformationSituation.Hom σ τ)
          (hf : f.toRingHom = DeformationSituation.ringHomIdOver hσ hτ),
          (homologyTensor 𝒟.complex 2).map
              (DeformationSituation.kernelMapOver hσ hτ f hf) (𝒟.obstruction hσ) =
            𝒟.obstruction hτ) ∧
      ∀ {σ : DeformationSituation X} (hσ : σ.IsOver 𝒟.toObjectOverSpec),
        Nonempty (DeformationSituation.ObjectLift σ) ↔ 𝒟.obstruction hσ = 0 :=
  sorry

/-- The derived object of the stored complex in the derived category of the coefficient ring. -/
def derivedObject (𝒟 : DualObstruction X) :
    DerivedCategory (ModuleCat 𝒟.carrier) :=
  DerivedCategory.Q.obj 𝒟.complex

/-- The derived object is the image of the stored complex under localization. -/
theorem derivedObject_eq (𝒟 : DualObstruction X) :
    𝒟.derivedObject = DerivedCategory.Q.obj 𝒟.complex :=
  sorry

/-- The obstruction vanishes exactly when the deformation situation admits an object lift. -/
theorem obstruction_eq_zero_iff_nonempty_objectLift (𝒟 : DualObstruction X)
    {σ : DeformationSituation X} (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.obstruction hσ = 0 ↔ Nonempty (DeformationSituation.ObjectLift σ) :=
  sorry

end DualObstruction

end AlgebraicGeometry.GroupoidsOver
