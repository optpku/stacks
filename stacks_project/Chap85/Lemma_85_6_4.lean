module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Injective

/-!
# Lemma 85.6.4

In Situation 85.3.3, restriction to degree `n` preserves injective module
sheaves when the maps `f_φ⁻¹ O_n ⟶ O_m` are flat for every `φ : n ⟶ m`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite

universe u v w

namespace CategoryTheory.SimplicialSites

/- Lemma 85.6.4. In the continuous-site presentation, restriction to a fixed
degree preserves injective module sheaves under outgoing flatness. -/
@[stacks 0D75] #check (CategoryTheory.SimplicialSites.modulePullback_preservesInjectiveObjects :
  ∀
    (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
    [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
    [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
      ((C.map φ).toFunctor).op.HasLeftKanExtension P]
    [IsMorphismDiagram C J]
    [UnivLE.{max u v, w}]
    (O : Sheaf (topology C J) RingCat.{w})
    [(topology C J).HasSheafCompose (forget RingCat.{w})]
    [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
    [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
    [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
      (ofStage C n).op.HasPointwiseRightKanExtension P]
    [HasWeakSheafify (topology C J) (Type w)]
    (n : SimplexCategory)
    (h_flat : ∀ {m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (ringedToposMap C J O φ)),
    ((stageMorphism C J O n).modulePullback).PreservesInjectiveObjects)

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

/- Lemma 85.6.4. In the cocontinuous fiber presentation, restriction to a fixed
degree preserves injective module sheaves under outgoing flatness. -/
@[stacks 0D75] #check (CategoryTheory.Grothendieck.fiberModulePullback_preservesInjectiveObjects :
  ∀
    (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
    [IsFiberwiseSite F J]
    [UnivLE.{max u v, w}]
    (O : Sheaf (topology F J) RingCat.{w})
    [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
    [HasSheafify (topology F J) (Type w)]
    [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
      (ι F (op n)).op.HasPointwiseRightKanExtension P]
    [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
      ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
    (n : SimplexCategory)
    (h_flat : ∀ {m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (fiberRingedToposMap F J O φ)),
    ((fiberStageMorphism F J O n).modulePullback).PreservesInjectiveObjects)

end CategoryTheory.Grothendieck
