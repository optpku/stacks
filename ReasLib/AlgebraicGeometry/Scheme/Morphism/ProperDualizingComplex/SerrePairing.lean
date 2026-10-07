module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.PerfectPairing
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.Hom
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

namespace ProperDualizingComplex

/-- The tensor-shift identification from `ω_X[i] ⊗ Eᵛ` to the corresponding
shift of `ω_X^• ⊗ Eᵛ`. -/
noncomputable def serreTensorShiftIso
    {k : Type u} [Field k] {X : Scheme.{u}}
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    [Scheme.CohenMacaulay X] [EquidimensionalSpace X]
    (d : ℕ) (h_dimension : topologicalKrullDim X = d)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) (i : ℤ) :
    (moduleObject (dualizingModuleQCoh f)⟦i⟧).obj ⊗
        MonoidalClosed.dual ((VectorBundleK0.toPerfect X).obj E).obj ≅
      (properDualizingComplex f).obj⟦i - (d : ℤ)⟧ ⊗
        MonoidalClosed.dual ((VectorBundleK0.toPerfect X).obj E).obj :=
  let j := i - (d : ℤ)
  let ω := moduleObject (dualizingModuleQCoh f)
  let shiftIso :
      (properDualizingComplex f).obj⟦j⟧ ≅ ω⟦i⟧.obj :=
    ((DerivedQCoh.inclusion X).commShiftIso j).symm.app
        (properDualizingComplex f) ≪≫
      (DerivedQCoh.inclusion X).mapIso
        ((shiftFunctor (DerivedQCoh X) j).mapIso
          (dualizingModuleShiftIso f d
            (dimensionIndex_eq_of_topologicalKrullDim_eq f d h_dimension)
            (properDualizingComplex_concentrated f d h_dimension))) ≪≫
      (DerivedQCoh.inclusion X).mapIso
        ((shiftFunctorAdd' (DerivedQCoh X) (d : ℤ) j i
          ((add_sub_assoc (d : ℤ) i d).symm.trans
            (add_sub_cancel_left (d : ℤ) i))).symm.app ω)
  shiftIso.symm ⊗ᵢ
    Iso.refl (MonoidalClosed.dual ((VectorBundleK0.toPerfect X).obj E).obj)

/-- The induced linear equivalence from the source-facing
`Hⁱ(X, ω_X ⊗ Eᵛ)` carrier to the first carrier of the derived trace pairing. -/
noncomputable def serreLeftEquiv
    {k : Type u} [Field k] {X : Scheme.{u}}
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    [Scheme.CohenMacaulay X] [EquidimensionalSpace X]
    (d : ℕ) (h_dimension : topologicalKrullDim X = d)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) (i : ℤ) :
    DerivedExt.value f (𝟙_ (RingedSpace.ModuleDerived X.toRingedSpace))
        ((moduleObject (dualizingModuleQCoh f)⟦i⟧).obj ⊗
          MonoidalClosed.dual ((VectorBundleK0.toPerfect X).obj E).obj) 0 ≃ₗ[k]
      DerivedExt.value f (𝟙_ (RingedSpace.ModuleDerived X.toRingedSpace))
        ((properDualizingComplex f).obj⟦i - (d : ℤ)⟧ ⊗
          MonoidalClosed.dual ((VectorBundleK0.toPerfect X).obj E).obj) 0 :=
  (((DerivedExt.bifunctor f 0).obj
    (Opposite.op (𝟙_ (RingedSpace.ModuleDerived X.toRingedSpace)))).mapIso
      (serreTensorShiftIso f d h_dimension E i)).toLinearEquiv

/-- The degree reindexing from `Hᵈ⁻ⁱ(X, E)` to the second carrier of the
degree-`i - d` derived trace pairing. -/
noncomputable def serreRightEquiv
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (d : ℕ)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) (i : ℤ) :
    cohomologyOverField f
        ((@coherentBoundedToDerivedQCoh X
          (LocallyOfFiniteType.isLocallyNoetherian f)).obj
            ((@Scheme.K0.perfectToBoundedCoherent X
              (FiniteType.isNoetherian f)).obj ((VectorBundleK0.toPerfect X).obj E)))
        ((d : ℤ) - i) ≃ₗ[k]
      cohomologyOverField f
        ((@coherentBoundedToDerivedQCoh X
          (LocallyOfFiniteType.isLocallyNoetherian f)).obj
            ((@Scheme.K0.perfectToBoundedCoherent X
              (FiniteType.isNoetherian f)).obj ((VectorBundleK0.toPerfect X).obj E)))
        (-(i - (d : ℤ))) :=
  (eqToIso (congrArg (cohomologyOverField f
    ((@coherentBoundedToDerivedQCoh X
      (LocallyOfFiniteType.isLocallyNoetherian f)).obj
        ((@Scheme.K0.perfectToBoundedCoherent X
          (FiniteType.isNoetherian f)).obj ((VectorBundleK0.toPerfect X).obj E))))
    (Int.neg_sub i (d : ℤ)).symm)).toLinearEquiv

/-- The trace pairing on the source-facing carriers
`Hⁱ(X, ω_X ⊗ Eᵛ)` and `Hᵈ⁻ⁱ(X, E)`. -/
noncomputable def serrePairingWith
    {k : Type u} [Field k] {X : Scheme.{u}}
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (e : fieldObject k ≅ ModuleCat.of k k)
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    [Scheme.CohenMacaulay X] [EquidimensionalSpace X]
    (d : ℕ) (h_dimension : topologicalKrullDim X = d)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) (i : ℤ) :=
  (perfectPairingWith e f ((VectorBundleK0.toPerfect X).obj E) (i - (d : ℤ))).compl₁₂
    (serreLeftEquiv f d h_dimension E i).toLinearMap
    (serreRightEquiv f d E i).toLinearMap

/-- The finite-locally-free Serre pairing is the derived perfect-complex pairing in
degree `i - d`. -/
theorem serrePairingWith_def
    {k : Type u} [Field k] {X : Scheme.{u}}
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (e : fieldObject k ≅ ModuleCat.of k k)
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    [Scheme.CohenMacaulay X] [EquidimensionalSpace X]
    (d : ℕ) (h_dimension : topologicalKrullDim X = d)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) (i : ℤ) :
    serrePairingWith e f d h_dimension E i =
      (perfectPairingWith e f ((VectorBundleK0.toPerfect X).obj E)
        (i - (d : ℤ))).compl₁₂
          (serreLeftEquiv f d h_dimension E i).toLinearMap
          (serreRightEquiv f d E i).toLinearMap := sorry

/-- Evaluation of the finite-locally-free Serre pairing is the trace of cup product
followed by the dual evaluation map. -/
theorem serrePairingWith_apply
    {k : Type u} [Field k] {X : Scheme.{u}}
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (e : fieldObject k ≅ ModuleCat.of k k)
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    [Scheme.CohenMacaulay X] [EquidimensionalSpace X]
    (d : ℕ) (h_dimension : topologicalKrullDim X = d)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) (i : ℤ)
    (ξ : DerivedExt.value f (𝟙_ (RingedSpace.ModuleDerived X.toRingedSpace))
      ((moduleObject (dualizingModuleQCoh f)⟦i⟧).obj ⊗
        MonoidalClosed.dual ((VectorBundleK0.toPerfect X).obj E).obj) 0)
    (η : cohomologyOverField f
      ((@coherentBoundedToDerivedQCoh X
        (LocallyOfFiniteType.isLocallyNoetherian f)).obj
          ((@Scheme.K0.perfectToBoundedCoherent X
            (FiniteType.isNoetherian f)).obj
              ((VectorBundleK0.toPerfect X).obj E))) ((d : ℤ) - i)) :
    serrePairingWith e f d h_dimension E i ξ η =
      traceWith e f
        (cohomologyOverFieldMap f
          (ShiftedHom.sourceShiftEquiv
            ((@coherentBoundedToDerivedQCoh X
              (LocallyOfFiniteType.isLocallyNoetherian f)).obj
                ((@Scheme.K0.perfectToBoundedCoherent X
                  (FiniteType.isNoetherian f)).obj
                    ((VectorBundleK0.toPerfect X).obj E)))
            (properDualizingComplex f) (i - (d : ℤ))
            (ambientExtLift f (i - (d : ℤ))
              ((@coherentBoundedToDerivedQCoh X
                (LocallyOfFiniteType.isLocallyNoetherian f)).obj
                  ((@Scheme.K0.perfectToBoundedCoherent X
                    (FiniteType.isNoetherian f)).obj
                      ((VectorBundleK0.toPerfect X).obj E)))
              (perfectTensorExtComparison f
                ((VectorBundleK0.toPerfect X).obj E) (i - (d : ℤ))
                  (serreLeftEquiv f d h_dimension E i ξ)))) 0
          ((cohomologyNegShiftIso f (i - (d : ℤ))
            ((@coherentBoundedToDerivedQCoh X
              (LocallyOfFiniteType.isLocallyNoetherian f)).obj
                ((@Scheme.K0.perfectToBoundedCoherent X
                  (FiniteType.isNoetherian f)).obj
                    ((VectorBundleK0.toPerfect X).obj E)))).inv
              (serreRightEquiv f d E i η))) := sorry

/-- The finite-locally-free Serre pairing between the degree-`i` cohomology of
`ω_X ⊗ Eᵛ` and the degree-`d - i` cohomology of `E` is perfect. -/
instance serrePairingWith_isPerfPair
    {k : Type u} [Field k] {X : Scheme.{u}}
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (e : fieldObject k ≅ ModuleCat.of k k)
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    [Scheme.CohenMacaulay X] [EquidimensionalSpace X]
    (d : ℕ) (h_dimension : topologicalKrullDim X = d)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) (i : ℤ) :
    LinearMap.IsPerfPair (serrePairingWith e f d h_dimension E i) := sorry
end ProperDualizingComplex

end AlgebraicGeometry.Scheme.DerivedQCoh
