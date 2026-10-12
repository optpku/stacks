/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import stacks_project.Chap90.Definition_90_3_1_Classical
public import stacks_project.Chap90.Definition_90_6_1_Prorepresentable
public import stacks_project.Chap90.Definition_90_10_1_DualNumber
public import stacks_project.Chap90.Definition_90_23_1_Smooth
public import stacks_project.Chap90.Remarks_90_5_2_IsoClass
public import stacks_project.Chap93.Lemma_93_10_3_Deformation

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

namespace FlatSchemeMorphismCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The set-valued functor sending `A` to the isomorphism classes of objects of
`Def_{X ⟶ Y}(A)`. -/
abbrev isoClassFunctor (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    ArtinianLocalAlgCat Λ k ⥤ Type (u + 1) :=
  fiberIsoClassFunctor (deformationForget Λ k X Y f hX hY hf)

/-- The value of `isoClassFunctor` at `A` is the type of isomorphism classes in the
fibre of `deformationForget` over `A`. -/
theorem isoClassFunctor_obj (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    (A : ArtinianLocalAlgCat Λ k) :
    (isoClassFunctor Λ k X Y f hX hY hf).obj A =
      isomorphismClasses.obj
        (Cat.of ((deformationForget Λ k X Y f hX hY hf).Fiber A)) :=
  sorry

/-- Lemma 93.10.5 (1)
In Example 93.10.1 assume `X ⟶ Y` is a morphism of proper `k`-schemes. Assume
`Λ` is a complete local ring with residue field `k` (the classical case). Then
the functor `F` sending `A` to the isomorphism classes of objects of
`Def_{X ⟶ Y}(A)`, i.e. `F(A) = Ob(Def_{X ⟶ Y}(A))/≅`, has a hull. -/
@[stacks 0ET6]
theorem exists_isHull (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    [IsProper hX] [IsProper hY] [ArtinianLocalAlgCat.IsClassical Λ k] :
    ∃ R : CompleteLocalAlgCat Λ k,
      ∃ η : CompleteLocalAlgCat.restrictedCoyoneda R ⋙ uliftFunctor.{u + 1, u} ⟶
          isoClassFunctor Λ k X Y f hX hY hf,
        NatTrans.IsSmooth η ∧
          Function.Bijective (η.app (ArtinianLocalAlgCat.dualNumber Λ k)) :=
  sorry

/-- Lemma 93.10.5 (2)
In Example 93.10.1, with the same properness and classical assumptions, if
`Der_k(O_X, O_X) = Der_k(O_Y, O_Y) = 0`, then the functor `F` sending `A` to
`Ob(Def_{X ⟶ Y}(A))/≅` is prorepresentable. -/
@[stacks 0ET6]
theorem isProrepresentable_isoClass (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    [IsProper hX] [IsProper hY] [ArtinianLocalAlgCat.IsClassical Λ k]
    (h_derX : Subsingleton
      (Hom.derivations hX.toShHom
        (SheafOfModules.unit X.toRingedSpace.ringCatSheaf)))
    (h_derY : Subsingleton
      (Hom.derivations hY.toShHom
        (SheafOfModules.unit Y.toRingedSpace.ringCatSheaf))) :
    ∃ R : CompleteLocalAlgCat Λ k,
      Nonempty
        (CompleteLocalAlgCat.restrictedCoyoneda R ⋙ uliftFunctor.{u + 1, u} ≅
          isoClassFunctor Λ k X Y f hX hY hf) :=
  sorry

end FlatSchemeMorphismCat
