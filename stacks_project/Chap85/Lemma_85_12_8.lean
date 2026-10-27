/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.CartesianHomology
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.CartesianHomology
public import ReasLib.CategoryTheory.Sites.Grothendieck.CartesianHomology
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberCartesianHomology
import StacksCheckRecall

/-!
# Lemma 85.12.8

Cartesian derived objects are characterized by their homology sheaves; the module
criterion assumes flatness of every coface morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (f : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map f).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram.{u, v, w} C J]

section Abelian

variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (f : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map f).toFunctor).op.HasLeftKanExtension P]

section AbelianDerived

variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/- Lemma 85.12.8 (1): The abelian criterion in the morphism-of-sites presentation. -/
@[stacks 0D7L] #check (CategoryTheory.SimplicialSites.AbelianDerived.isCartesian_iff_homology C J :
  ∀ (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})),
    AbelianDerived.IsCartesian C J K ↔
      ∀ q : ℤ, Abelian.IsCartesian C J
        ((DerivedCategory.homologyFunctor
          (Sheaf (topology C J) AddCommGrpCat.{w}) q).obj K))

/- The forward abelian inference API. -/
#check (CategoryTheory.SimplicialSites.AbelianDerived.instHomology_isCartesian C J :
  ∀ (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    [AbelianDerived.IsCartesian C J K] (q : ℤ),
    Abelian.IsCartesian C J
      ((DerivedCategory.homologyFunctor
        (Sheaf (topology C J) AddCommGrpCat.{w}) q).obj K))

/- The reverse abelian inference API. -/
#check (CategoryTheory.SimplicialSites.AbelianDerived.instIsCartesian_of_homology C J :
  ∀ (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    [∀ q : ℤ, Abelian.IsCartesian C J
      ((DerivedCategory.homologyFunctor
        (Sheaf (topology C J) AddCommGrpCat.{w}) q).obj K)],
    AbelianDerived.IsCartesian C J K)

end AbelianDerived

end Abelian

section Modules

variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (f : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O f).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
variable [∀ {m n : SimplexCategory} (f : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O f)]

/- Lemma 85.12.8 (2): The module criterion in the morphism-of-sites presentation. -/
@[stacks 0D7L] #check (CategoryTheory.SimplicialSites.ModuleDerived.isCartesian_iff_homology C J O :
  ∀ (h_flat : ∀ {n : ℕ} (j : Fin (n + 2)),
      ToposHom.IsFlat (ringedToposMap C J O (SimplexCategory.δ j)))
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J O)),
    ModuleDerived.IsCartesian C J O K ↔
      ∀ q : ℤ, Module.IsCartesian C J O
        (Hom.ModuleDerived.cohomologySheaf (totalRingedSite C J O) K q))

/- The forward module criterion. -/
#check (CategoryTheory.SimplicialSites.ModuleDerived.homology_isCartesian C J O :
  ∀ (h_flat : ∀ {n : ℕ} (j : Fin (n + 2)),
      ToposHom.IsFlat (ringedToposMap C J O (SimplexCategory.δ j)))
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J O))
    [ModuleDerived.IsCartesian C J O K] (q : ℤ),
    Module.IsCartesian C J O
      (Hom.ModuleDerived.cohomologySheaf (totalRingedSite C J O) K q))

/- The reverse module criterion. -/
#check (CategoryTheory.SimplicialSites.ModuleDerived.isCartesian_of_homology C J O :
  ∀ (h_flat : ∀ {n : ℕ} (j : Fin (n + 2)),
      ToposHom.IsFlat (ringedToposMap C J O (SimplexCategory.δ j)))
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J O))
    (hK : ∀ q : ℤ, Module.IsCartesian C J O
      (Hom.ModuleDerived.cohomologySheaf (totalRingedSite C J O) K q)),
    ModuleDerived.IsCartesian C J O K)

end Modules

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]

section Abelian

variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/- Lemma 85.12.8 (3): The abelian criterion in the fiberwise presentation. -/
@[stacks 0D7L] #check (CategoryTheory.Grothendieck.AbelianDerived.isCartesian_iff_homology F J :
  ∀ (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})),
    AbelianDerived.IsCartesian F J K ↔
      ∀ q : ℤ, Sheaf.IsCartesian F J AddCommGrpCat.{w}
        ((DerivedCategory.homologyFunctor
          (Sheaf (topology F J) AddCommGrpCat.{w}) q).obj K))

end Abelian

section Modules

open Opposite

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

/- Lemma 85.12.8 (4): The module criterion in the fiberwise presentation. -/
@[stacks 0D7L] #check (CategoryTheory.Grothendieck.ModuleDerived.isCartesian_iff_homology F J O :
  ∀ (h_flat : ∀ (n : ℕ) (j : Fin (n + 2)),
      ToposHom.IsFlat (fiberRingedToposMap F J O (SimplexCategory.δ j)))
    (K : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O)),
    ModuleDerived.IsCartesian F J O K ↔
      ∀ q : ℤ, Module.IsCartesian F J O
        (Hom.ModuleDerived.cohomologySheaf (fiberTotalRingedSite F J O) K q))

end Modules

end CategoryTheory.Grothendieck
