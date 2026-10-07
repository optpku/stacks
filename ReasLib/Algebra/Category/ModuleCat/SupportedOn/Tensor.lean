module

public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedAction
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Derived
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic

@[expose] public section

open CategoryTheory
open DerivedCategory
open DerivedCategory.DerivedTensor
open DerivedCategory.DerivedTensor.Bifunctor.Right
open DerivedCategory.DerivedTensor.Right

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

namespace DerivedSections

/-- The ambient value of derived sections has cohomology supported on `T`. -/
theorem objCohomologyIn
    (T : Set (PrimeSpectrum A)) (K : DerivedCategory (ModuleCat.{u} A)) :
    DerivedCategory.cohomologyIn (ModuleCat.supportedOn T)
      ((derivedSections T ⋙ derivedInclusion T).obj K) := sorry

/-- Tensoring on the right preserves supported cohomology in the left factor. -/
theorem tensorCohomologyInLeft
    (T : Set (PrimeSpectrum A)) (K L : DerivedCategory (ModuleCat.{u} A))
    (hK : DerivedCategory.cohomologyIn (ModuleCat.supportedOn T) K) :
    DerivedCategory.cohomologyIn (ModuleCat.supportedOn T)
      (DerivedTensor.Right.obj K L) := sorry

/-- Tensoring on the left preserves supported cohomology in the right factor. -/
theorem tensorCohomologyInRight
    (T : Set (PrimeSpectrum A)) (K L : DerivedCategory (ModuleCat.{u} A))
    (hL : DerivedCategory.cohomologyIn (ModuleCat.supportedOn T) L) :
    DerivedCategory.cohomologyIn (ModuleCat.supportedOn T)
      (DerivedTensor.Right.obj K L) := sorry

/-- Under the finite-dimensional hypothesis, the derived-sections counit is invertible on
objects whose cohomology is supported on `T`. -/
theorem counitIsIso
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : DerivedCategory.cohomologyIn (ModuleCat.supportedOn T) K) :
    IsIso ((derivedAdjunction T).counit.app K) := sorry

/-- The canonical map from a supported-cohomology object to its derived sections. -/
noncomputable def toObj
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : DerivedCategory.cohomologyIn (ModuleCat.supportedOn T) K) :
    K ⟶ (derivedSections T ⋙ derivedInclusion T).obj K :=
  @inv _ _ _ _ ((derivedAdjunction T).counit.app K)
    (counitIsIso T hT hfinite K hK)

/-- The canonical map to derived sections is inverse to the derived adjunction counit. -/
theorem toObj_comp_counit
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : DerivedCategory.cohomologyIn (ModuleCat.supportedOn T) K) :
    toObj T hT hfinite K hK ≫ (derivedAdjunction T).counit.app K = 𝟙 K := sorry

/-- The map on fixed-right derived tensor products induced by maps in both variables. -/
noncomputable def tensorMap
    {K K' L L' : DerivedCategory (ModuleCat.{u} A)} (f : K ⟶ K') (g : L ⟶ L') :
    DerivedTensor.Right.obj K L ⟶ DerivedTensor.Right.obj K' L' :=
  (isoApp L K).hom ≫ Bifunctor.functor.map (Prod.mkHom f g) ≫ (isoApp L' K').inv

/-- `tensorMap` is the two-variable derived tensor map transported to the fixed-right model. -/
theorem tensorMap_def
    {K K' L L' : DerivedCategory (ModuleCat.{u} A)} (f : K ⟶ K') (g : L ⟶ L') :
    tensorMap f g =
      (isoApp L K).hom ≫ Bifunctor.functor.map (Prod.mkHom f g) ≫ (isoApp L' K').inv := sorry

/-- Coreflect a map out of an object with supported cohomology. -/
noncomputable def lift
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A)
    {K L : DerivedCategory (ModuleCat.{u} A)}
    (hK : DerivedCategory.cohomologyIn (ModuleCat.supportedOn T) K) (f : K ⟶ L) :
    K ⟶ (derivedSections T ⋙ derivedInclusion T).obj L :=
  toObj T hT hfinite K hK ≫
    (derivedSections T ⋙ derivedInclusion T).map f

/-- Composing the lifted map with the derived-adjunction counit recovers the ambient map. -/
theorem lift_comp_counit
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A)
    {K L : DerivedCategory (ModuleCat.{u} A)}
    (hK : DerivedCategory.cohomologyIn (ModuleCat.supportedOn T) K) (f : K ⟶ L) :
    lift T hT hfinite hK f ≫ (derivedAdjunction T).counit.app L = f := sorry

/-- The ambient map from `RΓ_T(A) ⊗[A]^L K` to `K`, induced by the derived adjunction
counit and the regular-module action. -/
noncomputable def tensorRegularTo
    (T : Set (PrimeSpectrum A)) (K : DerivedCategory (ModuleCat.{u} A)) :
    DerivedTensor.Right.obj
        ((derivedSections T ⋙ derivedInclusion T).obj
          (ModuleCat.single0 (ModuleCat.of A A))) K ⟶ K :=
  tensorMap ((derivedAdjunction T).counit.app
      (ModuleCat.single0 (ModuleCat.of A A))) (𝟙 K) ≫
    (ModuleCat.DerivedAction.fixedRightActionIso K).hom

/-- The regular supported tensor map is the tensor of the counit with the identity, followed by
the regular-module action. -/
theorem tensorRegularTo_def
    (T : Set (PrimeSpectrum A)) (K : DerivedCategory (ModuleCat.{u} A)) :
    tensorRegularTo T K =
      tensorMap ((derivedAdjunction T).counit.app
          (ModuleCat.single0 (ModuleCat.of A A))) (𝟙 K) ≫
        (ModuleCat.DerivedAction.fixedRightActionIso K).hom := sorry

/-- The canonical comparison from `RΓ_T(A) ⊗[A]^L K` to `RΓ_T(K)`. -/
noncomputable def tensorComparison
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    DerivedTensor.Right.obj
        ((derivedSections T ⋙ derivedInclusion T).obj
          (ModuleCat.single0 (ModuleCat.of A A))) K ⟶
      (derivedSections T ⋙ derivedInclusion T).obj K :=
  lift T hT hfinite
    (tensorCohomologyInLeft T _ _
      (objCohomologyIn T (ModuleCat.single0 (ModuleCat.of A A))))
    (tensorRegularTo T K)

/-- Composing `tensorComparison` with the derived-adjunction counit recovers the regular
supported tensor map. -/
theorem tensorComparison_comp_counit
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    tensorComparison T hT hfinite K ≫ (derivedAdjunction T).counit.app K =
      tensorRegularTo T K := sorry

/-- The canonical comparison `RΓ_T(A) ⊗[A]^L K ⟶ RΓ_T(K)` is invertible. -/
noncomputable instance tensorComparison_isIso
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    IsIso (tensorComparison T hT hfinite K) := sorry

/-- The canonical comparison from `K ⊗[A]^L RΓ_T(L)` to
`RΓ_T(K ⊗[A]^L L)`. -/
noncomputable def tensorComparisonRight
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A)
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    DerivedTensor.Right.obj K ((derivedSections T ⋙ derivedInclusion T).obj L) ⟶
      (derivedSections T ⋙ derivedInclusion T).obj (DerivedTensor.Right.obj K L) :=
  lift T hT hfinite
    (tensorCohomologyInRight T _ _ (objCohomologyIn T L))
    (tensorMap (𝟙 K) ((derivedAdjunction T).counit.app L))

/-- Composing `tensorComparisonRight` with the derived-adjunction counit recovers tensoring
the identity of `K` with the counit at `L`. -/
theorem tensorComparisonRight_comp_counit
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A)
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    tensorComparisonRight T hT hfinite K L ≫
        (derivedAdjunction T).counit.app (DerivedTensor.Right.obj K L) =
      tensorMap (𝟙 K) ((derivedAdjunction T).counit.app L) := sorry

/-- The canonical comparison `K ⊗[A]^L RΓ_T(L) ⟶ RΓ_T(K ⊗[A]^L L)` is invertible. -/
noncomputable instance tensorComparisonRight_isIso
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A)
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    IsIso (tensorComparisonRight T hT hfinite K L) := sorry

/-- The canonical comparison from `RΓ_T(K) ⊗[A]^L L` to
`RΓ_T(K ⊗[A]^L L)`. -/
noncomputable def tensorComparisonLeft
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A)
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    DerivedTensor.Right.obj ((derivedSections T ⋙ derivedInclusion T).obj K) L ⟶
      (derivedSections T ⋙ derivedInclusion T).obj (DerivedTensor.Right.obj K L) :=
  lift T hT hfinite
    (tensorCohomologyInLeft T _ _ (objCohomologyIn T K))
    (tensorMap ((derivedAdjunction T).counit.app K) (𝟙 L))

/-- Composing `tensorComparisonLeft` with the derived-adjunction counit recovers tensoring
the counit at `K` with the identity of `L`. -/
theorem tensorComparisonLeft_comp_counit
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A)
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    tensorComparisonLeft T hT hfinite K L ≫
        (derivedAdjunction T).counit.app (DerivedTensor.Right.obj K L) =
      tensorMap ((derivedAdjunction T).counit.app K) (𝟙 L) := sorry

/-- The canonical comparison `RΓ_T(K) ⊗[A]^L L ⟶ RΓ_T(K ⊗[A]^L L)` is invertible. -/
noncomputable instance tensorComparisonLeft_isIso
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A)
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    IsIso (tensorComparisonLeft T hT hfinite K L) := sorry

/-- The canonical comparison from `RΓ_T(K) ⊗[A]^L RΓ_T(L)` to
`RΓ_T(K ⊗[A]^L L)`. -/
noncomputable def tensorComparisonBoth
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A)
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    DerivedTensor.Right.obj ((derivedSections T ⋙ derivedInclusion T).obj K)
        ((derivedSections T ⋙ derivedInclusion T).obj L) ⟶
      (derivedSections T ⋙ derivedInclusion T).obj (DerivedTensor.Right.obj K L) :=
  lift T hT hfinite
    (tensorCohomologyInLeft T _ _ (objCohomologyIn T K))
    (tensorMap ((derivedAdjunction T).counit.app K)
      ((derivedAdjunction T).counit.app L))

/-- Composing `tensorComparisonBoth` with the derived-adjunction counit recovers tensoring
the counits at `K` and `L`. -/
theorem tensorComparisonBoth_comp_counit
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A)
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    tensorComparisonBoth T hT hfinite K L ≫
        (derivedAdjunction T).counit.app (DerivedTensor.Right.obj K L) =
      tensorMap ((derivedAdjunction T).counit.app K)
        ((derivedAdjunction T).counit.app L) := sorry

/-- The canonical comparison `RΓ_T(K) ⊗[A]^L RΓ_T(L) ⟶ RΓ_T(K ⊗[A]^L L)` is invertible. -/
noncomputable instance tensorComparisonBoth_isIso
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A)
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    IsIso (tensorComparisonBoth T hT hfinite K L) := sorry

/-- If either factor has cohomology supported on `T`, then their derived tensor product does too. -/
theorem tensor_mem
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A)
    (K L : DerivedCategory (ModuleCat.{u} A))
    (hKL : DerivedCategory.cohomologyIn (ModuleCat.supportedOn T) K ∨
      DerivedCategory.cohomologyIn (ModuleCat.supportedOn T) L) :
    DerivedCategory.cohomologyIn (ModuleCat.supportedOn T)
      (DerivedTensor.Right.obj K L) := sorry

end DerivedSections

end CategoryTheory.ModuleCat.SupportedOn
