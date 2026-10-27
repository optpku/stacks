/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.DerivedModuleSystem.Descent
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.DerivedModuleSystem.FiberDescent
import StacksCheckRecall

/-!
# Lemma 85.14.6

In Situation 85.3.3, a morphism of associated simplicial systems of objects
`K, K'` of `D(O)` is induced by a morphism `K ⟶ K'` when every `f_φ⁻¹ O_n ⟶ O_m`
is flat, `K` is cartesian, and `Hom(K_i⟦i - 1⟧, K'_i) = 0` for `i > 1`.

The two checks cover case A, presented by continuous site functors, and case B,
presented by cocontinuous fiber functors. In the library convention, the ringed
topos morphism attached to `φ : m ⟶ n` goes from stage `n` to stage `m`, so its
inverse-image structure map is `f_φ⁻¹ O_m ⟶ O_n`. Flatness refers to extension
of scalars along this structure map; the source uses the opposite subscript
convention in its displayed flatness hypothesis.
-/

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialSites
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [instMorphismDiagram : IsMorphismDiagram.{u, v, w} C J]
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

/- Lemma 85.14.6 (1)
In case A of Situation 85.3.3, let `O` be a sheaf of rings on `C_total`. If `K, K'` are
objects of `D(O)`, assume `f_φ⁻¹ O_n ⟶ O_m` is flat for `φ : m ⟶ n`, `K` is
cartesian, and `Hom(K_i⟦i - 1⟧, K'_i) = 0` for `i > 1`. Then every morphism of
associated simplicial systems `{K_n ⟶ K'_n}` comes from a morphism `K ⟶ K'` in
`D(O)`. -/
@[stacks 0D9S] #check (CategoryTheory.SimplicialSites.exists_hom_of_toDerivedModuleSystemHom C J O :
  ∀ (K K' : Hom.ModuleDerived.{w} (totalRingedSite C J O))
    [ModuleDerived.IsCartesian C J O K]
    (h_flat : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ToposHom.IsFlat (ringedToposMap C J O φ))
    (h_hom : ∀ (n : SimplexCategory), 1 < n.len →
      Subsingleton
        (((toDerivedModuleSystem C J O K).obj n)⟦(n.len : ℤ) - 1⟧ ⟶
          (toDerivedModuleSystem C J O K').obj n))
    (α : RingedSite.Simplicial.DerivedModuleSystem.Hom (toDerivedModuleSystem C J O K)
      (toDerivedModuleSystem C J O K')),
    ∃ f : K ⟶ K', ∀ n, (toDerivedModuleSystemMap C J O f).app n = α.app n)

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

open Opposite

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable (O : Sheaf (topology F J) RingCat.{w})

variable [UnivLE.{max u v, w}]
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (fiberStageMorphism F J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (fiberRingedToposMap F J O φ)]

/- Lemma 85.14.6 (2)
In case B of Situation 85.3.3, flat transition structure maps, cartesianness of
`K`, and `Hom(K_i⟦i - 1⟧, K'_i) = 0` for `i > 1` imply that every morphism of
the associated fiberwise systems lifts to a morphism `K ⟶ K'` on the total site. -/
@[stacks 0D9S] #check (CategoryTheory.Grothendieck.exists_hom_of_toDerivedModuleSystemHom F J O :
  ∀ (K K' : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O))
    [ModuleDerived.IsCartesian F J O K]
    (h_flat : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ToposHom.IsFlat (fiberRingedToposMap F J O φ))
    (h_hom : ∀ (n : SimplexCategory), 1 < n.len →
      Subsingleton
        (((toDerivedModuleSystem F J O K).obj n)⟦(n.len : ℤ) - 1⟧ ⟶
          (toDerivedModuleSystem F J O K').obj n))
    (α : RingedSite.Simplicial.DerivedModuleSystem.Hom (toDerivedModuleSystem F J O K)
      (toDerivedModuleSystem F J O K')),
    ∃ f : K ⟶ K', ∀ n, (toDerivedModuleSystemMap F J O f).app n = α.app n)

end CategoryTheory.Grothendieck
