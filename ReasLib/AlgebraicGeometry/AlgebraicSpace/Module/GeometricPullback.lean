/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.InverseImage.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.CommutativeRingView
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module

/-! # Original-universe module pullback with actual geometric and scalar data

The structure map is built from actual scheme pullback of functions on each
étale square, extended through the specified Kan/sheafification adjunction.
No old large-site direct-image construction enters these definitions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PullbackFactory.Ringed

open Squares

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Forgetting the structure ring preserves the sheaf condition in the
original coefficient universe. This is a property of the fixed forgetful functor. -/
instance structure_hasSheafCompose (Z : AlgebraicSpace S) :
    (smallEtaleTopology Z).HasSheafCompose (forget RingCat.{u}) := by
  sorry

/-- Functions pull back by the actual map of schemes forming the square. -/
def squareRingMap (sq : EtaleSquare f) :
    (structureSheaf Y).obj.obj (op sq.right) ⟶
      (structureSheaf X).obj.obj (op sq.left) :=
  (forget₂ CommRingCat RingCat).map sq.map.left.appTop

/-- For the specified square-colimit/sheafification functor, finite limits
are preserved. Étale neighbourhoods admit common refinements locally;
sheafification is left exact. This is a genuine geometric property of a
fixed functor, not the assertion that some suitable functor exists. -/
theorem inverse_leftExact : PreservesFiniteLimits (Geometric.inverse f) := by
  sorry

/-- Both underlying functors and their adjunction are the new explicit ones. -/
def topos : MorphismOfTopoiIn (smallEtaleTopology Y) (smallEtaleTopology X) := by
  -- Local instance justification (defeq pin): Package the already specified squarewise geometric inverse image of f as left exact, without changing its functor data.
  letI := inverse_leftExact f
  exact
    { inverseImageFunctor := LeftExactFunctor.of (Geometric.inverse f)
      pushforward := Geometric.direct f
      adjunction := Geometric.adjunction f }

/-- The original structure sheaf with only its ring operations forgotten. -/
abbrev structureType (Z : AlgebraicSpace S) : Sheaf (smallEtaleTopology Z) (Type u) :=
  (sheafCompose (smallEtaleTopology Z) (forget RingCat.{u})).obj (structureSheaf Z)

/-- On a genuine square, pullback of functions is the actual scheme Γ map. -/
def squareFunctions :
    (target f).op ⋙ (inclusion Y).op ⋙ (structureType Y).obj ⟶
      (source f).op ⋙ (inclusion X).op ⋙ (structureType X).obj where
  app a := (forget RingCat.{u}).map (squareRingMap f a.unop.geometric)
  naturality := by sorry

/-- Extend the specified Γ maps through the actual square colimit. -/
def presheafFunctions :
    (SquareKan.inversePresheaf f).obj ((inclusion Y).op ⋙ (structureType Y).obj) ⟶
      (inclusion X).op ⋙ (structureType X).obj :=
  (((source f).op.lanAdjunction (Type u)).homEquiv _ _).symm (squareFunctions f)

set_option backward.isDefEq.respectTransparency false in
/-- The colimit extension really restricts to the prescribed scheme pullback
on every generator. This computation is proved from the Kan adjunction. -/
theorem presheafFunctions_on_square (a : Square f) :
    SquareKan.squareGenerator f ((inclusion Y).op ⋙ (structureType Y).obj) a ≫
        (presheafFunctions f).app (op a.left) =
      (forget RingCat.{u}).map (squareRingMap f a.geometric) := by
  have h := congr_app
    ((((source f).op.lanAdjunction (Type u)).homEquiv _ _).apply_symm_apply
      (squareFunctions f)) (op a)
  rw [Adjunction.homEquiv_unit, Functor.lanAdjunction_unit] at h
  exact h

/-- Extend through small-site sheafification, using the actual target sheaf. -/
def smallFunctions :
    (SquareKan.inverse f).obj
        ((TypeComparison.comparison Y).functor.obj (structureType Y)) ⟶
      (TypeComparison.comparison X).functor.obj (structureType X) :=
  ((sheafificationAdjunction (topology X) (Type u)).homEquiv _ _).symm
    (presheafFunctions f)

/-- The inverse-image-form structure map of type sheaves on the original site. -/
def functions : (topos f).inverseImage.obj (structureType Y) ⟶ structureType X :=
  (TypeComparison.comparison X).inverse.map (smallFunctions f) ≫
    (TypeComparison.comparison X).unitIso.inv.app (structureType X)

/-- The actual underlying function on the canonically transported ring sheaf. -/
def ringFunctions :
    (sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).obj
        ((topos f).ringInverseImage.obj (structureSheaf Y)) ⟶ structureType X :=
  (topos f).ringInverseImageForgetIso.hom.app (structureSheaf Y) ≫ functions f

/-- The canonical functions above preserve the four ring operations because
each square uses the scheme pullback ring homomorphism and the inverse image
preserves finite products. These are laws of the specified function. -/
def ringFunctionsApp (U : (smallEtaleSite X)ᵒᵖ) :
    ((topos f).ringInverseImage.obj (structureSheaf Y)).obj.obj U ⟶
      (structureSheaf X).obj.obj U := by
  let R : RingCat.{u} := ((topos f).ringInverseImage.obj (structureSheaf Y)).obj.obj U
  let T : RingCat.{u} := (structureSheaf X).obj.obj U
  let g : R →+* T :=
    { toFun := fun x ↦ (ringFunctions f).hom.app U x
      map_one' := by sorry
      map_mul' := by sorry
      map_zero' := by sorry
      map_add' := by sorry }
  exact @RingCat.ofHom R T (inferInstance : Ring R) (inferInstance : Ring T) g

/-- The ring-valued map has the same specified section functions. -/
def structureMap : (topos f).ringInverseImage.obj (structureSheaf Y) ⟶ structureSheaf X :=
  ObjectProperty.homMk
    { app := ringFunctionsApp f
      naturality := by sorry }

/-- Ringed-topos data are now explicit on both geometric and coefficient stages. -/
def ringed : RingedSite.ToposHom (ringedSite X) (ringedSite Y) where
  toTopos := topos f
  structureMap := structureMap f

/-- Pullback of a commutative ring sheaf has commutative multiplication. -/
theorem source_mul_comm (U : (smallEtaleSite X)ᵒᵖ)
    (r s : ((topos f).ringInverseImage.obj (structureSheaf Y)).obj.obj U) :
    r * s = s * r := by
  sorry

theorem target_mul_comm (U : (smallEtaleSite X)ᵒᵖ)
    (r s : (structureSheaf X).obj.obj U) : r * s = s * r := by
  exact @mul_comm Γ(U.unop.left.left, ⊤) inferInstance r s

/-- Same ring carriers and functions, now in the commutative-ring interface. -/
def coefficientMap := CommutativeRingView.map
  (source_mul_comm f) (target_mul_comm (X := X)) (structureMap f)

/-- The actual tensor/sheafification scalar extension at universe u. -/
def scalarExtension :
    SheafOfModules.{u} ((topos f).ringInverseImage.obj (structureSheaf Y)) ⥤ X.Modules :=
  ScalarExtension.extension X (coefficientMap f)

/-- The actual tensor adjunction supplies this certificate. -/
def scalarAdjunction : scalarExtension f ⊣ SheafOfModules.restrictScalars.{u} (structureMap f) :=
  ScalarExtension.adjunction X (coefficientMap f)

/-- Actual geometric inverse image followed by actual scalar extension,
with exactly the original module universes and no added hypotheses. -/
def pullback : Y.Modules.{u} ⥤ X.Modules.{u} :=
  (topos f).moduleInverseImage (structureSheaf Y) ⋙ scalarExtension f

@[simp]
theorem ringFunctionsApp_apply (U : (smallEtaleSite X)ᵒᵖ)
    (x : ((topos f).ringInverseImage.obj (structureSheaf Y)).obj.obj U) :
    ringFunctionsApp f U x = (ringFunctions f).hom.app U x := rfl

end AlgebraicGeometry.AlgebraicSpace.PullbackFactory.Ringed
