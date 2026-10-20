module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.LowerShriek
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Fiber
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Flat

/-!
# Exactness of module lower shriek on ringed simplicial sites

The module lower-shriek functor from a fixed degree is exact when every outgoing
simplex operator induces a flat morphism of ringed topoi.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable [UnivLE.{max u v, w}]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (topology C J) (Type w)]

/-- Module lower shriek from a fixed degree of a simplicial diagram of sites is
exact if every outgoing simplex operator induces a flat morphism of ringed topoi. -/
theorem moduleLowerShriek_exact (n : SimplexCategory)
    (h_flat : ∀ {m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (ringedToposMap C J O φ)) :
    exactFunctor
      (SheafOfModules.{w} (componentRingSheaf C J O n))
      (SheafOfModules.{w} O)
      (moduleLowerShriek C J O n) :=
  sorry

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable [UnivLE.{max u v, w}]
variable (O : Sheaf (topology F J) RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

/-- Module lower shriek from a fixed fiber of a simplicial object of sites is
exact if every outgoing simplex operator induces a flat morphism of ringed topoi. -/
theorem fiberModuleLowerShriek_exact (n : SimplexCategory)
    (h_flat : ∀ {m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (fiberRingedToposMap F J O φ)) :
    exactFunctor
      (SheafOfModules.{w} (fiberComponentRingSheaf F J O n))
      (SheafOfModules.{w} O)
      (fiberModuleLowerShriek F J O n) :=
  sorry

end CategoryTheory.Grothendieck
