/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SchemeMorphism.Hull
import StacksCheckRecall

/-!
# Hull and prorepresentability for morphisms of proper schemes

In Example 93.10.1, if `X ⟶ Y` is a morphism of proper `k`-schemes and `Λ` is
classical, the functor of isomorphism classes of objects of `Def_{X ⟶ Y}` has a
hull. If additionally `Der_k(O_X, O_X) = Der_k(O_Y, O_Y) = 0`, that functor is
prorepresentable.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Lemma 93.10.5 (1)
In Example 93.10.1 assume `X ⟶ Y` is a morphism of proper `k`-schemes. Assume
`Λ` is a complete local ring with residue field `k` (the classical case). Then
the functor `F` sending `A` to the isomorphism classes of objects of
`Def_{X ⟶ Y}(A)`, i.e. `F(A) = Ob(Def_{X ⟶ Y}(A))/≅`, has a hull. -/
@[stacks 0ET6] #check (FlatSchemeMorphismCat.exists_isHull Λ k :
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [IsProper hX] [IsProper hY] [ArtinianLocalAlgCat.IsClassical Λ k],
    ∃ R : CompleteLocalAlgCat Λ k,
      ∃ η : CompleteLocalAlgCat.restrictedCoyoneda R ⋙ uliftFunctor.{u + 1, u} ⟶
          FlatSchemeMorphismCat.isoClassFunctor Λ k X Y f hX hY hf,
        NatTrans.IsSmooth η ∧
          Function.Bijective (η.app (ArtinianLocalAlgCat.dualNumber Λ k)))

/- Lemma 93.10.5 (2)
In Example 93.10.1, with the same properness and classical assumptions, if
`Der_k(O_X, O_X) = Der_k(O_Y, O_Y) = 0`, then the functor `F` sending `A` to
`Ob(Def_{X ⟶ Y}(A))/≅` is prorepresentable. -/
@[stacks 0ET6] #check (FlatSchemeMorphismCat.isProrepresentable_isoClass Λ k :
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [IsProper hX] [IsProper hY] [ArtinianLocalAlgCat.IsClassical Λ k]
    (h_derX : Subsingleton
      (Hom.derivations hX.toShHom
        (SheafOfModules.unit X.toRingedSpace.ringCatSheaf)))
    (h_derY : Subsingleton
      (Hom.derivations hY.toShHom
        (SheafOfModules.unit Y.toRingedSpace.ringCatSheaf))),
    ∃ R : CompleteLocalAlgCat Λ k,
      Nonempty
        (CompleteLocalAlgCat.restrictedCoyoneda R ⋙ uliftFunctor.{u + 1, u} ≅
          FlatSchemeMorphismCat.isoClassFunctor Λ k X Y f hX hY hf))

variable (X Y : Scheme.{u}) (f : X ⟶ Y)
  (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
  (hf : f ≫ hY = hX)

-- The object formula is the specialization of the generic fibre-evaluation theorem.
#check (CategoryTheory.Functor.fiberIsoClassFunctor.obj
  (FlatSchemeMorphismCat.deformationForget Λ k X Y f hX hY hf) :
  ∀ A : ArtinianLocalAlgCat Λ k,
    (FlatSchemeMorphismCat.isoClassFunctor Λ k X Y f hX hY hf).obj A =
      isomorphismClasses.obj
        (Cat.of ((FlatSchemeMorphismCat.deformationForget Λ k X Y f hX hY hf).Fiber A)))
