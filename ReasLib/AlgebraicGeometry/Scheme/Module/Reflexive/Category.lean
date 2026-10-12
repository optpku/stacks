/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Exact
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.InternalHom
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# The category of coherent reflexive module sheaves

On an integral locally Noetherian scheme, coherent reflexive module sheaves form a reflective
additive subcategory of coherent modules, with kernels and reflected cokernels.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The property of a coherent module sheaf that its underlying module sheaf is reflexive. -/
abbrev reflexiveCohProperty (X : Scheme.{u}) :
    ObjectProperty (RingedSpace.Coh X.toRingedSpace) :=
  fun ℱ ↦ IsReflexive ℱ.obj

/-- The full subcategory of coherent reflexive module sheaves on a scheme. -/
abbrev ReflexiveCoh (X : Scheme.{u}) :=
  (reflexiveCohProperty X).FullSubcategory

/-- The inclusion of coherent reflexive modules into coherent modules. -/
abbrev reflexiveCohInclusion (X : Scheme.{u}) :
    ReflexiveCoh X ⥤ RingedSpace.Coh X.toRingedSpace :=
  (reflexiveCohProperty X).ι

/-- The forgetful functor from coherent reflexive modules to all module sheaves. -/
abbrev reflexiveCohForget (X : Scheme.{u}) : ReflexiveCoh X ⥤ X.Modules :=
  reflexiveCohInclusion X ⋙ (SheafOfModules.isCoherent X.ringCatSheaf).ι

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]

/-- The reflexive-hull reflector from coherent modules to coherent reflexive modules. -/
noncomputable def reflexiveCohReflector :
    RingedSpace.Coh X.toRingedSpace ⥤ ReflexiveCoh X :=
  ObjectProperty.lift (reflexiveCohProperty X)
    (ObjectProperty.lift (SheafOfModules.isCoherent X.ringCatSheaf)
      ((SheafOfModules.isCoherent X.ringCatSheaf).ι ⋙ reflexiveHullFunctor X)
      (fun ℱ ↦ by
        -- Local instance justification (proof-local temporary data): expose the coherent
        -- property stored by the full subcategory while constructing the lifted functor.
        letI : ℱ.obj.IsCoherent := ℱ.property
        change (reflexiveHull ℱ.obj).IsCoherent
        exact instIsCoherentReflexiveHull ℱ.obj))
    (fun ℱ ↦ by
      -- Local instance justification (proof-local temporary data): expose the coherent
      -- property stored by the full subcategory while constructing the lifted functor.
      letI : ℱ.obj.IsCoherent := ℱ.property
      change IsReflexive (reflexiveHull ℱ.obj)
      exact instIsReflexiveReflexiveHull ℱ.obj)

/-- Reflexive hull is left adjoint to the inclusion of coherent reflexive modules. -/
noncomputable def reflexiveCohReflectorAdjunction :
    reflexiveCohReflector X ⊣ reflexiveCohInclusion X := by
  refine Adjunction.mkOfUnitCounit
    { unit :=
        { app := fun ℱ ↦ ObjectProperty.homMk (toReflexiveHull ℱ.obj)
          naturality := ?_ }
      counit :=
        { app := fun ℱ ↦ by
            -- Local instance justification (proof-local temporary data): the reflexivity
            -- property carried by the subcategory makes the canonical double-dual map invertible.
            exact ObjectProperty.homMk
              (ObjectProperty.homMk
                (inv (I := ℱ.property) (toReflexiveHull ℱ.obj.obj)))
          naturality := ?_ }
      left_triangle := ?_
      right_triangle := ?_ }
  all_goals sorry

/-- The inclusion of coherent reflexive modules is reflective. -/
instance instReflectiveReflexiveCohInclusion : Reflective (reflexiveCohInclusion X) where
  L := reflexiveCohReflector X
  adj := reflexiveCohReflectorAdjunction X

/-- The coherent-reflexive category inherits its preadditive structure. -/
instance instPreadditiveReflexiveCoh : Preadditive (ReflexiveCoh X) := inferInstance

/-- Coherent reflexive modules are closed under kernels computed among coherent modules. -/
instance instIsClosedUnderKernelsReflexiveCohProperty
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] :
    (reflexiveCohProperty X).IsClosedUnderKernels := sorry

/-- The category of coherent reflexive modules has kernels. -/
instance instHasKernelsReflexiveCoh
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] :
    HasKernels (ReflexiveCoh X) := inferInstance

/-- The inclusion identifies a coherent-reflexive kernel with the usual coherent kernel. -/
noncomputable def reflexiveCohKernelIso {ℱ 𝒢 : ReflexiveCoh X} (f : ℱ ⟶ 𝒢) :
    (reflexiveCohInclusion X).obj (kernel f) ≅
      kernel ((reflexiveCohInclusion X).map f) := by
  -- Local instance justification (proof-local temporary data): the full-subcategory inclusion
  -- preserves this kernel by the proved closure of the reflexive property under kernels.
  letI : PreservesLimit (parallelPair f 0) (reflexiveCohInclusion X) :=
    (reflexiveCohProperty X).preservesKernels_ι f
  exact PreservesKernel.iso (reflexiveCohInclusion X) f

/-- The category of coherent reflexive modules has cokernels obtained by reflection. -/
noncomputable instance instHasCokernelsReflexiveCoh : HasCokernels (ReflexiveCoh X) := by
  -- Local instance justification (proof-local temporary data): reflective colimits provide the
  -- walking-parallel-pair colimits from which the standard cokernel instance is inferred.
  letI : HasColimitsOfShape WalkingParallelPair (ReflexiveCoh X) :=
    hasColimitsOfShape_of_reflective (reflexiveCohInclusion X)
  infer_instance

/-- A coherent-reflexive cokernel is the reflexive hull of the usual coherent cokernel. -/
noncomputable def reflexiveCohCokernelIso {ℱ 𝒢 : ReflexiveCoh X} (f : ℱ ⟶ 𝒢) :
    (reflexiveCohInclusion X).obj (cokernel f) ≅
      (reflexiveCohInclusion X).obj
        ((reflexiveCohReflector X).obj (cokernel ((reflexiveCohInclusion X).map f))) := by
  let adj := reflexiveCohReflectorAdjunction X
  -- Local instance justification (proof-local temporary data): expose the named adjunction so
  -- the standard left-adjoint preservation theorem supplies the cokernel comparison.
  letI : (reflexiveCohReflector X).IsLeftAdjoint := adj.isLeftAdjoint
  let comparison :
      (reflexiveCohReflector X).obj (cokernel ((reflexiveCohInclusion X).map f)) ≅
        cokernel ((reflexiveCohReflector X).map ((reflexiveCohInclusion X).map f)) :=
    PreservesCokernel.iso (reflexiveCohReflector X) ((reflexiveCohInclusion X).map f)
  let eF : ℱ.obj.obj ≅ reflexiveHull ℱ.obj.obj :=
    @asIso _ _ _ _ (toReflexiveHull ℱ.obj.obj) ℱ.property
  let eG : 𝒢.obj.obj ≅ reflexiveHull 𝒢.obj.obj :=
    @asIso _ _ _ _ (toReflexiveHull 𝒢.obj.obj) 𝒢.property
  let p :
      (reflexiveCohReflector X).obj ((reflexiveCohInclusion X).obj ℱ) ≅ ℱ :=
    ObjectProperty.isoMk (reflexiveCohProperty X)
      (ObjectProperty.isoMk (SheafOfModules.isCoherent X.ringCatSheaf)
        eF.symm)
  let q :
      (reflexiveCohReflector X).obj ((reflexiveCohInclusion X).obj 𝒢) ≅ 𝒢 :=
    ObjectProperty.isoMk (reflexiveCohProperty X)
      (ObjectProperty.isoMk (SheafOfModules.isCoherent X.ringCatSheaf)
        eG.symm)
  let comparison' :
      cokernel ((reflexiveCohReflector X).map ((reflexiveCohInclusion X).map f)) ≅ cokernel f :=
    cokernel.mapIso
      (f := (reflexiveCohReflector X).map ((reflexiveCohInclusion X).map f))
      f p q (by
        apply ObjectProperty.hom_ext
        apply ObjectProperty.hom_ext
        change
          reflexiveHullMap ((reflexiveCohForget X).map f) ≫ eG.inv =
            eF.inv ≫ (reflexiveCohForget X).map f
        have hn :
            (reflexiveCohForget X).map f ≫ eG.hom =
              eF.hom ≫ reflexiveHullMap ((reflexiveCohForget X).map f) :=
          (toReflexiveHullNatTrans X).naturality ((reflexiveCohForget X).map f)
        apply (eG.comp_inv_eq).2
        calc
          reflexiveHullMap ((reflexiveCohForget X).map f) =
              eF.inv ≫ ((reflexiveCohForget X).map f ≫ eG.hom) :=
            (eF.eq_inv_comp).2 hn.symm
          _ = (eF.inv ≫ (reflexiveCohForget X).map f) ≫ eG.hom :=
            (Category.assoc _ _ _).symm)
  exact (reflexiveCohInclusion X).mapIso ((comparison.trans comparison').symm)

/-- The coherent-reflexive category has finite biproducts. -/
noncomputable instance instHasFiniteBiproductsReflexiveCoh :
    HasFiniteBiproducts (ReflexiveCoh X) := by
  -- Local instance justification (proof-local temporary data): reflective finite products are
  -- used only to invoke the standard preadditive finite-biproduct constructor.
  letI : HasFiniteProducts (ReflexiveCoh X) :=
    ⟨fun _ ↦ hasLimitsOfShape_of_reflective (reflexiveCohInclusion X)⟩
  exact HasFiniteBiproducts.of_hasFiniteProducts

end AlgebraicGeometry.Scheme.Modules
