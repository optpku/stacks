/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Cartesian
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Flat

@[expose] public section

open CategoryTheory
open scoped Simplicial
open RingedSite
open Opposite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [instMorphismDiagram : IsMorphismDiagram C J]
include instMorphismDiagram instWeakSheafify instLeftKan
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]

namespace ModuleDerived

/-- A morphism from a cartesian derived module object is zero if its degree-zero
component is zero, all simplex-operator structure maps are flat, and the component
Hom groups vanish in shifts `n` for `n > 0` and `n + 1` for `n ≥ 0`. -/
theorem hom_eq_zero
    (K K' : Hom.ModuleDerived.{w} (totalRingedSite C J O))
    [ModuleDerived.IsCartesian C J O K]
    (h_flat : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ToposHom.IsFlat (ringedToposMap C J O φ))
    (h_hom : ∀ n : SimplexCategory, 0 < n.len →
      Subsingleton (((moduleDerivedComponent C J O n).obj K)⟦(n.len : ℤ)⟧ ⟶
        (moduleDerivedComponent C J O n).obj K'))
    (h_hom_succ : ∀ n : SimplexCategory,
      Subsingleton (((moduleDerivedComponent C J O n).obj K)⟦(n.len + 1 : ℤ)⟧ ⟶
        (moduleDerivedComponent C J O n).obj K'))
    (f : K ⟶ K') (hf0 : (moduleDerivedComponent C J O ⦋0⦌).map f = 0) :
    f = 0 := sorry

/-- Morphisms from a cartesian derived module object are equal when their degree-zero
components agree, all simplex-operator structure maps are flat, and the component
Hom groups vanish in shifts `n` for `n > 0` and `n + 1` for `n ≥ 0`. -/
theorem hom_ext
    (K K' : Hom.ModuleDerived.{w} (totalRingedSite C J O))
    [ModuleDerived.IsCartesian C J O K]
    (h_flat : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ToposHom.IsFlat (ringedToposMap C J O φ))
    (h_hom : ∀ n : SimplexCategory, 0 < n.len →
      Subsingleton (((moduleDerivedComponent C J O n).obj K)⟦(n.len : ℤ)⟧ ⟶
        (moduleDerivedComponent C J O n).obj K'))
    (h_hom_succ : ∀ n : SimplexCategory,
      Subsingleton (((moduleDerivedComponent C J O n).obj K)⟦(n.len + 1 : ℤ)⟧ ⟶
        (moduleDerivedComponent C J O n).obj K'))
    (f g : K ⟶ K')
    (hfg : (moduleDerivedComponent C J O ⦋0⦌).map f =
      (moduleDerivedComponent C J O ⦋0⦌).map g) :
    f = g := sorry

end ModuleDerived

end CategoryTheory.SimplicialSites
