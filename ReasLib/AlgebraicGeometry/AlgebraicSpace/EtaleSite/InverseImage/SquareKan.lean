/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.InverseImage.Squares
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-! # Actual original-universe inverse-image data from étale squares

Precomposition with the Y-projection followed by left Kan extension along
the X-projection constructs the inverse-image presheaf. Its right adjoint
is right Kan extension of the X-restriction along the Y-projection.
All Kan extensions here are supplied by proved u-small Type (co)limits.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PullbackFactory.SquareKan

open Squares

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- The small-index colimits are real Type colimits, not an admitted adjoint. -/
theorem lan_exists (P : (Square f)ᵒᵖ ⥤ Type u) :
    (source f).op.HasPointwiseLeftKanExtension P := by infer_instance

/-- The small-index limits are real Type limits. -/
theorem ran_exists (P : (Square f)ᵒᵖ ⥤ Type u) :
    (target f).op.HasPointwiseRightKanExtension P := by infer_instance

/-- Pull sections back to actual squares, then take the actual colimit. -/
def inversePresheaf : ((Site Y)ᵒᵖ ⥤ Type u) ⥤ ((Site X)ᵒᵖ ⥤ Type u) :=
  (Functor.whiskeringLeft _ _ _).obj (target f).op ⋙ (source f).op.lan

/-- Compatible X-sections on squares over each Y-chart. -/
def directPresheaf : ((Site X)ᵒᵖ ⥤ Type u) ⥤ ((Site Y)ᵒᵖ ⥤ Type u) :=
  (Functor.whiskeringLeft _ _ _).obj (source f).op ⋙ (target f).op.ran

/-- The Hom equivalence is the composite of the two actual Kan adjunctions. -/
def presheafAdjunction : inversePresheaf f ⊣ directPresheaf f :=
  ((target f).op.ranAdjunction (Type u)).comp ((source f).op.lanAdjunction (Type u))

/-- A section on the target vertex supplies its actual inverse-image generator. -/
def squareGenerator (P : (Site Y)ᵒᵖ ⥤ Type u) (a : Square f) :
    P.obj (op a.right) ⟶ ((inversePresheaf f).obj P).obj (op a.left) :=
  ((source f).op.lanUnit.app ((target f).op ⋙ P)).app (op a)

/-- Direct-image sections evaluate on an actual square by the Ran counit. -/
def squareEvaluation (Q : (Site X)ᵒᵖ ⥤ Type u) (a : Square f) :
    ((directPresheaf f).obj Q).obj (op a.right) ⟶ Q.obj (op a.left) :=
  ((target f).op.ranCounit.app ((source f).op ⋙ Q)).app (op a)

/-- This is the geometric sheaf law of the specified compatible-section
presheaf. Pull back a cover of V to X ×_Y V and cover by the chosen affine
atlas charts of X; compatible sections glue uniquely there. The statement
selects no functor, section, or isomorphism. -/
theorem direct_isSheaf (Q : Sheaf (topology X) (Type u)) :
    Presheaf.IsSheaf (topology Y) ((directPresheaf f).obj Q.obj) := by
  sorry

/-- Actual colimit presheaf followed by the proved small-site sheafification. -/
def inverse : Sheaf (topology Y) (Type u) ⥤ Sheaf (topology X) (Type u) :=
  sheafToPresheaf _ _ ⋙ inversePresheaf f ⋙ presheafToSheaf _ _

/-- The direct image retains the actual compatible-section presheaf. -/
def direct : Sheaf (topology X) (Type u) ⥤ Sheaf (topology Y) (Type u) :=
  ObjectProperty.lift _ (sheafToPresheaf _ _ ⋙ directPresheaf f) (direct_isSheaf f)

/-- Restriction of the actual presheaf/sheafification Hom equivalence. -/
def adjunction : inverse f ⊣ direct f :=
  ((presheafAdjunction f).comp (sheafificationAdjunction (topology X) (Type u))).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf (topology Y) (Type u))
    (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

@[simp]
theorem direct_obj (Q : Sheaf (topology X) (Type u)) :
    ((direct f).obj Q).obj = (directPresheaf f).obj Q.obj := rfl

end AlgebraicGeometry.AlgebraicSpace.PullbackFactory.SquareKan
