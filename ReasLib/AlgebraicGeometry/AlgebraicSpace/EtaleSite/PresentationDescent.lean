/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationInclusion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Descent of étale sheaves along scheme presentations

Sections of the extension of a sheaf from scheme charts to algebraic spaces are
computed by the equalizer associated to a surjective étale scheme presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every algebraic space étale over `X` admits a surjective étale presentation
by a scheme étale over `X`. -/
theorem exists_surjectiveEtaleSchemeCover {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : spacesEtaleSite X) :
    ∃ (U' : smallEtaleSite X) (π : (smallEtaleToSpaces X).obj U' ⟶ U),
      Representable.Etale π.left ∧ Function.Surjective (Points.map π.left) :=
  sorry

/-- A surjective morphism from a scheme étale over `X` gives a singleton cover
in the spaces-étale precoverage. -/
theorem ofArrows_schemeCover_mem_spacesEtalePrecoverage {S : Scheme.{u}}
    {X : AlgebraicSpace S} {U : spacesEtaleSite X} {U' : smallEtaleSite X}
    (π : (smallEtaleToSpaces X).obj U' ⟶ U)
    (hπ : Function.Surjective (Points.map π.left)) :
    Presieve.ofArrows (fun _ : PUnit.{u + 1} ↦ (smallEtaleToSpaces X).obj U') (fun _ ↦ π) ∈
      spacesEtalePrecoverage X U :=
  sorry

/-- The kernel pair of an étale morphism from a scheme to an algebraic space
étale over `X` is represented by a scheme étale over `X`. -/
theorem exists_kernelPair_of_isEtaleFromScheme {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : spacesEtaleSite X} {U' : smallEtaleSite X}
    (π : (smallEtaleToSpaces X).obj U' ⟶ U) (hp : Representable.Etale π.left) :
    ∃ (R : smallEtaleSite X) (fst snd : R ⟶ U'),
      IsPullback (ofOverMap fst.left) (ofOverMap snd.left) π.left π.left :=
  sorry

/-- The right Kan extension counit compares the extended sheaf's sections on
a scheme chart with the original sheaf's sections. -/
def spacesEtaleExtension_obj_smallEtale {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) (U' : smallEtaleSite X) :
    ((smallEtalePresentationExtension X).obj F).obj.obj
        (op ((smallEtaleToSpaces X).obj U')) ⟶ F.obj.obj (op U') :=
  ((smallEtaleToSpaces X).op.ranCounit.app F.obj).app (op U')

/-- The comparison on a scheme chart is the right Kan extension counit component. -/
theorem spacesEtaleExtension_obj_smallEtale_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) (U' : smallEtaleSite X) :
    spacesEtaleExtension_obj_smallEtale F U' =
      ((smallEtaleToSpaces X).op.ranCounit.app F.obj).app (op U') :=
  rfl

/-- A spaces-étale sheaf restricts to `F` up to isomorphism exactly when it is
isomorphic to the right Kan extension of `F`. -/
theorem unique_spacesEtaleExtension {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    (G : Sheaf (spacesEtaleTopology X) (Type (u + 1))) :
    Nonempty ((smallEtalePresentationRestriction X).obj G ≅ F) ↔
      Nonempty (G ≅ (smallEtalePresentationExtension X).obj F) :=
  sorry

/-- Restriction along an arrow from a scheme chart, followed by the right Kan
counit, maps extended sections to sections of the original sheaf. -/
def spacesEtaleExtension_restrict {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    {U : spacesEtaleSite X} {U' : smallEtaleSite X}
    (π : (smallEtaleToSpaces X).obj U' ⟶ U) :
    ((smallEtalePresentationExtension X).obj F).obj.obj (op U) ⟶ F.obj.obj (op U') :=
  ((smallEtalePresentationExtension X).obj F).obj.map π.op ≫
    spacesEtaleExtension_obj_smallEtale F U'

/-- The section comparison is restriction along `π` followed by the counit. -/
theorem spacesEtaleExtension_restrict_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    {U : spacesEtaleSite X} {U' : smallEtaleSite X}
    (π : (smallEtaleToSpaces X).obj U' ⟶ U) :
    spacesEtaleExtension_restrict F π =
      ((smallEtalePresentationExtension X).obj F).obj.map π.op ≫
        spacesEtaleExtension_obj_smallEtale F U' :=
  rfl

/-- The section comparison equalizes the two restriction maps induced by a
scheme kernel pair. -/
theorem spacesEtaleExtension_equalizer_condition {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    {U : spacesEtaleSite X} {U' R : smallEtaleSite X}
    (π : (smallEtaleToSpaces X).obj U' ⟶ U) (fst snd : R ⟶ U')
    (h_pair : IsPullback (ofOverMap fst.left) (ofOverMap snd.left) π.left π.left) :
    spacesEtaleExtension_restrict F π ≫ F.obj.map fst.op =
      spacesEtaleExtension_restrict F π ≫ F.obj.map snd.op :=
  sorry

/-- A surjective scheme presentation maps extended sections into the equalizer
of the original sheaf's two kernel-pair restriction maps. -/
def spacesEtaleExtension_toEqualizer {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    {U : spacesEtaleSite X} {U' R : smallEtaleSite X}
    (π : (smallEtaleToSpaces X).obj U' ⟶ U) (fst snd : R ⟶ U')
    (hπ : Function.Surjective (Points.map π.left))
    (h_pair : IsPullback (ofOverMap fst.left) (ofOverMap snd.left) π.left π.left) :
    ((smallEtalePresentationExtension X).obj F).obj.obj (op U) ⟶
      { x : F.obj.obj (op U') // F.obj.map fst.op x = F.obj.map snd.op x } :=
  TypeCat.ofHom fun s ↦
    ⟨spacesEtaleExtension_restrict F π s,
      ConcreteCategory.congr_hom
        (spacesEtaleExtension_equalizer_condition F π fst snd h_pair) s⟩

/-- The equalizer comparison sends a section to its restriction followed by
the right Kan counit. -/
theorem spacesEtaleExtension_toEqualizer_apply {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    {U : spacesEtaleSite X} {U' R : smallEtaleSite X}
    (π : (smallEtaleToSpaces X).obj U' ⟶ U) (fst snd : R ⟶ U')
    (hπ : Function.Surjective (Points.map π.left))
    (h_pair : IsPullback (ofOverMap fst.left) (ofOverMap snd.left) π.left π.left)
    (s : ((smallEtalePresentationExtension X).obj F).obj.obj (op U)) :
    (spacesEtaleExtension_toEqualizer F π fst snd hπ h_pair s).val =
      spacesEtaleExtension_restrict F π s :=
  rfl

/-- Sections of the extended sheaf are isomorphic to the equalizer of the
original sheaf's restriction maps on a surjective scheme presentation's kernel pair. -/
instance isIso_spacesEtaleExtension_toEqualizer {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    {U : spacesEtaleSite X} {U' R : smallEtaleSite X}
    (π : (smallEtaleToSpaces X).obj U' ⟶ U) (fst snd : R ⟶ U')
    (hπ : Function.Surjective (Points.map π.left))
    (h_pair : IsPullback (ofOverMap fst.left) (ofOverMap snd.left) π.left π.left) :
    IsIso (spacesEtaleExtension_toEqualizer F π fst snd hπ h_pair) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
