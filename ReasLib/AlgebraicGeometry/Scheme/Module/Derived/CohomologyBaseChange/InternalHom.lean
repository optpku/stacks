/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.Finiteness
public import ReasLib.CategoryTheory.Monoidal.Closed.PullbackComparison

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
open DerivedCategory.TStructure
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.ModuleDerived
open AlgebraicGeometry.Scheme.ModuleDerived.InternalHom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

section Construction

variable {X' X : Scheme.{u}}
variable [KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [KFlat.TensorDescends X.toRingedSpace]
variable [KFlat.IsLocalization X.toRingedSpace]
variable [KFlat.HomotopyTensorDescends X'.toRingedSpace]
variable [KFlat.TensorDescends X'.toRingedSpace]
variable [KFlat.IsLocalization X'.toRingedSpace]

/-- The derived internal Hom equipped with an explicit proof that its cohomology is
quasicoherent. -/
noncomputable def internalHomObj {Y : Scheme.{u}}
    [KFlat.HomotopyTensorDescends Y.toRingedSpace]
    [KFlat.TensorDescends Y.toRingedSpace]
    [KFlat.IsLocalization Y.toRingedSpace]
    (H : MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace))
    (E : RingedSpace.ModuleDerived Y.toRingedSpace)
    (K : ModuleDerived.Quasicoherent Y)
    (h : ModuleDerived.quasicoherentProperty Y ((H.ihomOf E).obj K.obj)) :
    ModuleDerived.Quasicoherent Y :=
  ⟨(H.ihomOf E).obj K.obj, h⟩

/-- The underlying object of the quasicoherent internal-Hom lift is the selected derived
internal Hom. -/
theorem internalHomObj_obj {Y : Scheme.{u}}
    [KFlat.HomotopyTensorDescends Y.toRingedSpace]
    [KFlat.TensorDescends Y.toRingedSpace]
    [KFlat.IsLocalization Y.toRingedSpace]
    (H : MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace))
    (E : RingedSpace.ModuleDerived Y.toRingedSpace)
    (K : ModuleDerived.Quasicoherent Y)
    (h : ModuleDerived.quasicoherentProperty Y ((H.ihomOf E).obj K.obj)) :
    (internalHomObj H E K h).obj = (H.ihomOf E).obj K.obj := sorry

/-- Internal Hom from the pullback of a perfect complex into a derived quasicoherent object
again has quasicoherent cohomology. -/
theorem internalHomTarget_mem_of_isPerfect
    (g' : X' ⟶ X)
    (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (K' : ModuleDerived.Quasicoherent X')
    (hE : RingedSpace.ModuleDerived.IsPerfect E) :
    ModuleDerived.quasicoherentProperty X'
      ((H_X'.ihomOf
        ((RingedSpace.modulePullbackDerived g'.toShHom).obj E)).obj K'.obj) := sorry

variable (g' : X' ⟶ X)
variable [(RingedSpace.modulePullbackDerived g'.toShHom).Monoidal]

/-- The pullback/internal-Hom comparison followed by covariance in the target morphism,
lifted to derived objects with quasicoherent cohomology. -/
noncomputable def internalHomBaseChangeMap
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K')
    (h_source : ModuleDerived.quasicoherentProperty X
      ((H_X.ihomOf E).obj K.obj))
    (h_target : ModuleDerived.quasicoherentProperty X'
      ((H_X'.ihomOf
        ((RingedSpace.modulePullbackDerived g'.toShHom).obj E)).obj K'.obj)) :
    (pullback g').obj (internalHomObj H_X E K h_source) ⟶
      internalHomObj H_X'
        ((RingedSpace.modulePullbackDerived g'.toShHom).obj E) K' h_target :=
  ObjectProperty.homMk
    ((pullback.inclusionIso g').hom.app (internalHomObj H_X E K h_source) ≫
      Functor.PullbackInternalHom.comparisonOf H_X H_X'
        (RingedSpace.modulePullbackDerived g'.toShHom)
        (fun A B ↦ (Functor.Monoidal.μIso
          (RingedSpace.modulePullbackDerived g'.toShHom) A B).symm)
        E K.obj ≫
      (H_X'.ihomOf
        ((RingedSpace.modulePullbackDerived g'.toShHom).obj E)).map
          ((pullback.inclusionIso g').inv.app K ≫
            (ModuleDerived.Quasicoherent.inclusion X').map α))

/-- After forgetting quasicoherence, the internal-Hom base-change morphism is the canonical
pullback/internal-Hom comparison followed by the morphism induced by `α`. -/
theorem internalHomBaseChangeMap_obj
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K')
    (h_source : ModuleDerived.quasicoherentProperty X
      ((H_X.ihomOf E).obj K.obj))
    (h_target : ModuleDerived.quasicoherentProperty X'
      ((H_X'.ihomOf
        ((RingedSpace.modulePullbackDerived g'.toShHom).obj E)).obj K'.obj)) :
    (ModuleDerived.Quasicoherent.inclusion X').map
        (internalHomBaseChangeMap g' H_X H_X' E K K' α h_source h_target) =
      (pullback.inclusionIso g').hom.app (internalHomObj H_X E K h_source) ≫
        Functor.PullbackInternalHom.comparisonOf H_X H_X'
          (RingedSpace.modulePullbackDerived g'.toShHom)
          (fun A B ↦ (Functor.Monoidal.μIso
            (RingedSpace.modulePullbackDerived g'.toShHom) A B).symm)
          E K.obj ≫
        (H_X'.ihomOf
          ((RingedSpace.modulePullbackDerived g'.toShHom).obj E)).map
            ((pullback.inclusionIso g').inv.app K ≫
              (ModuleDerived.Quasicoherent.inclusion X').map α) := sorry

end Construction

/-- Under cohomology base change for `K ⟶ K'`, boundedness below of `K`, and
pseudo-coherence of `E`, the target internal Hom has quasicoherent cohomology. -/
theorem internalHomTarget_mem_of_pseudoCoherent
    {X' X S' S : Scheme.{u}}
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [KFlat.HomotopyTensorDescends X'.toRingedSpace]
    [KFlat.TensorDescends X'.toRingedSpace]
    [KFlat.IsLocalization X'.toRingedSpace]
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g)
    (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K')
    [∀ (x' : X') (i : ℤ), IsIso
      ((CohomologyBaseChangeModel.canonical g' f' f g sq).pointMap K K' α x' i)]
    (hK : (t.plus : ObjectProperty
      (RingedSpace.ModuleDerived X.toRingedSpace)) K.obj)
    (hE : RingedSpace.ModuleDerived.IsPseudoCoherent E) :
    ModuleDerived.quasicoherentProperty X'
      ((H_X'.ihomOf
        ((RingedSpace.modulePullbackDerived g'.toShHom).obj E)).obj K'.obj) := sorry

section Preservation

variable {X' X S' S : Scheme.{u}}
variable [KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [KFlat.TensorDescends X.toRingedSpace]
variable [KFlat.IsLocalization X.toRingedSpace]
variable [KFlat.HomotopyTensorDescends X'.toRingedSpace]
variable [KFlat.TensorDescends X'.toRingedSpace]
variable [KFlat.IsLocalization X'.toRingedSpace]
variable (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
variable [(RingedSpace.modulePullbackDerived g'.toShHom).Monoidal]
variable (sq : IsPullback g' f' f g)

/-- Pointwise cohomology base change is preserved by derived internal Hom from a perfect
ambient derived module. -/
theorem cohomologyBaseChange_internalHom_of_isPerfect
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
    (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K')
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    [∀ (x' : X') (i : ℤ), IsIso
      ((CohomologyBaseChangeModel.canonical g' f' f g sq).pointMap K K' α x' i)] :
    ∀ (x' : X') (i : ℤ), IsIso
      ((CohomologyBaseChangeModel.canonical g' f' f g sq).pointMap
        (internalHomObj H_X E K (derivedQCoh_of_perfect H_X E K hE))
        (internalHomObj H_X'
          ((RingedSpace.modulePullbackDerived g'.toShHom).obj E) K'
          (internalHomTarget_mem_of_isPerfect g' H_X' E K' hE))
        (internalHomBaseChangeMap g' H_X H_X' E K K' α
          (derivedQCoh_of_perfect H_X E K hE)
          (internalHomTarget_mem_of_isPerfect g' H_X' E K' hE)) x' i) := sorry

/-- If `K` is bounded below, pointwise cohomology base change is preserved by derived
internal Hom from a pseudo-coherent ambient derived module. -/
theorem cohomologyBaseChange_internalHom_of_isPseudoCoherent_of_boundedBelow
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
    (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K')
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hK : (t.plus : ObjectProperty
      (RingedSpace.ModuleDerived X.toRingedSpace)) K.obj)
    (hE : RingedSpace.ModuleDerived.IsPseudoCoherent E)
    [∀ (x' : X') (i : ℤ), IsIso
      ((CohomologyBaseChangeModel.canonical g' f' f g sq).pointMap K K' α x' i)] :
    ∀ (x' : X') (i : ℤ), IsIso
      ((CohomologyBaseChangeModel.canonical g' f' f g sq).pointMap
        (internalHomObj H_X E K
          (derivedQCoh_of_pseudoCoherent H_X E K hE hK))
        (internalHomObj H_X'
          ((RingedSpace.modulePullbackDerived g'.toShHom).obj E) K'
          (internalHomTarget_mem_of_pseudoCoherent
            g' f' f g sq H_X' E K K' α hK hE))
        (internalHomBaseChangeMap g' H_X H_X' E K K' α
          (derivedQCoh_of_pseudoCoherent H_X E K hE hK)
          (internalHomTarget_mem_of_pseudoCoherent
            g' f' f g sq H_X' E K K' α hK hE)) x' i) := sorry

end Preservation

end AlgebraicGeometry.Scheme.DerivedQCoh

end
