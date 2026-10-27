/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.QcqsAffine.BaseChange.DerivedHom.Colimit
import ReasLib.CategoryTheory.Sites.Sheafification.Abelian
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

/- Lemma 36.35.8: for the base-changed cofinal tail of a directed inverse system of
qcqs schemes with affine transition maps, the canonical cocone of derived Hom types is a
filtered colimit when `K₀` is pseudo-coherent and `L₀` has quasi-coherent cohomology and
locally finite Tor dimension relative to the base. -/
@[stacks 0DI7] #check
  (AlgebraicGeometry.Scheme.Limit.QcqsAffineLimit.homDiagram_isColimit_exists :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {D : OrderDual I ⥤ Scheme.{u}}
      [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
      [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]
      (s : Scheme.Limit.QcqsAffineLimit D) (X₀ : Scheme.{u})
      (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
      [Flat x₀] [Scheme.Hom.FinitePresentation x₀]
      [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase x₀.toShHom).carrier,
        DerivedCategory.DerivedTensor.Right.Has
          (C := RingedSpace.Modules
            ((RingedSpace.Hom.inverseImageBase x₀.toShHom).restrict U.isOpenEmbedding))]
      (K₀ L₀ : RingedSpace.ModuleDerived X₀.toRingedSpace),
      RingedSpace.ModuleDerived.IsPseudoCoherent K₀ →
        DerivedCategory.cohomologyIn
            (RingedSpace.quasiCoherentModuleProperty X₀.toRingedSpace) L₀ →
          RingedSpace.ModuleDerived.LocallyHasFiniteTorDimension
              (X := RingedSpace.Hom.inverseImageBase x₀.toShHom)
              ((RingedSpace.ModuleDerived.relativeRestriction
                x₀.toLRSHom.toShHom).obj L₀) →
            Nonempty (IsColimit (s.homDiagram x₀ K₀ L₀).cocone))
