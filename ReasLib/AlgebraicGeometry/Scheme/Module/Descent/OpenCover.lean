/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Descent.Canonical

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.QCoh.OpenCover

variable {S : Scheme.{u}}

/-- The canonical module descent functor for `𝒰` preserves componentwise
quasi-coherence. -/
theorem restrictionMapsTo (𝒰 : S.OpenCover.{v}) :
    Scheme.quasiCoherentModuleProperty S ≤
      (QCoh.descentProperty (fun i : 𝒰.I₀ ↦ 𝒰.X i) (fun i ↦ 𝒰.f i)).inverseImage
        (Modules.descentPseudofunctor.toDescentData (fun i : 𝒰.I₀ ↦ 𝒰.f i)) :=
  QCoh.canonicalFunctor_mapsTo (fun i : 𝒰.I₀ ↦ 𝒰.X i) (fun i ↦ 𝒰.f i)

/-- Restriction from global quasi-coherent modules to canonical descent data on `𝒰`. -/
noncomputable def restriction (𝒰 : S.OpenCover.{v}) :
    QCoh S ⥤ QCoh.DescentData (fun i : 𝒰.I₀ ↦ 𝒰.X i) (fun i ↦ 𝒰.f i) :=
  QCoh.canonicalFunctor (fun i : 𝒰.I₀ ↦ 𝒰.X i) (fun i ↦ 𝒰.f i)

namespace restriction

/-- The underlying canonical descent datum of a restricted quasi-coherent module. -/
theorem obj_obj (𝒰 : S.OpenCover.{v}) (F : QCoh S) :
    ((restriction 𝒰).obj F).obj =
      (Modules.descentPseudofunctor.toDescentData
        (fun i : 𝒰.I₀ ↦ 𝒰.f i)).obj F.obj :=
  QCoh.DescentData.canonical_obj (fun i : 𝒰.I₀ ↦ 𝒰.X i) (fun i ↦ 𝒰.f i) F

/-- The component at `i` of the canonical descent morphism of a restricted morphism. -/
theorem map_hom (𝒰 : S.OpenCover.{v}) {F G : QCoh S} (f : F ⟶ G) (i : 𝒰.I₀) :
    ((restriction 𝒰).map f).hom.hom i =
      (Modules.descentPseudofunctor.map (𝒰.f i).op.toLoc).toFunctor.map f.hom :=
  QCoh.canonicalFunctor.map_hom (fun i : 𝒰.I₀ ↦ 𝒰.X i) (fun i ↦ 𝒰.f i) f i

/-- Restriction to a scheme open cover is an equivalence on quasi-coherent modules. -/
instance isEquivalence (𝒰 : S.OpenCover.{v}) : (restriction 𝒰).IsEquivalence := sorry

/-- Restriction to a scheme open cover is fully faithful. -/
theorem fullyFaithful (𝒰 : S.OpenCover.{v}) :
    Nonempty (restriction 𝒰).FullyFaithful := sorry

end restriction

namespace DescentData

/-- Every canonical quasi-coherent descent datum on a scheme open cover is effective. -/
theorem isEffective (𝒰 : S.OpenCover.{v})
    (D : QCoh.DescentData (fun i : 𝒰.I₀ ↦ 𝒰.X i) (fun i ↦ 𝒰.f i)) :
    D.IsEffective := sorry

end DescentData

end AlgebraicGeometry.Scheme.QCoh.OpenCover
