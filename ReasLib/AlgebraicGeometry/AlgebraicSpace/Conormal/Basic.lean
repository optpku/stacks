/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Lemma_67_14_1_Quotient
public import stacks_project.Chap67.Lemma_67_28_12_IdealSheaf
public import stacks_project.Chap67.Remark_67_12_4_Coborder

/-!
# Conormal sheaves and total conormal algebras of immersions of algebraic spaces

The conormal sheaf of an immersion `i : Z ⟶ X` is `I / I²` for the coborder closed
immersion `Z ⟶ X \ ∂Z`, pulled back to `Z`. The total conormal algebra is the
associated graded `𝒪_Z`-algebra of that coborder ideal: the sectionwise associated
graded is sheafified on `X \ ∂Z`, pulled back along the coborder lift, and pushed
out along the inverse-image structure map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory Opposite AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Left Kan extensions of commutative-ring presheaves along the opposite of étale base
change exist on the small étale sites of algebraic spaces. -/
instance etaleBaseChange_op_hasLeftKanExtension_commRingCat
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (F : (smallEtaleSite Y)ᵒᵖ ⥤ CommRingCat.{u}) :
    (etaleBaseChange f).op.HasLeftKanExtension F :=
  sorry

/-- Commutative-ring-valued weak sheafification exists on the étale site of algebraic
spaces. -/
instance spacesEtaleTopology_hasWeakSheafify_commRingCat (X : AlgebraicSpace S) :
    HasWeakSheafify (spacesEtaleTopology X) CommRingCat.{u} :=
  sorry

/-- Commutative-ring-valued sheafification exists on the small étale site of an algebraic
space. -/
instance smallEtaleTopology_hasSheafify_commRingCat (X : AlgebraicSpace S) :
    HasSheafify (smallEtaleTopology X) CommRingCat.{u} :=
  sorry

/-- The coborder open `X \ ∂Z` supporting the closed-immersion factorization of an
immersion of algebraic spaces. -/
abbrev Hom.coborder {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] :
    AlgebraicSpace S :=
  (IsImmersion.coborderRange i).X

/-- `Hom.coborder i` is the underlying space of the coborder range of `i`. -/
theorem Hom.coborder_eq {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] :
    Hom.coborder i = (IsImmersion.coborderRange i).X :=
  rfl

namespace Hom

/-- The conormal sheaf `C_{Z/X}` of an immersion of algebraic spaces, as the pullback
to `Z` of `I / I²` for the coborder closed immersion `Z ⟶ X \ ∂Z`. -/
noncomputable def conormalSheaf {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] :
    Z.Modules :=
  (Modules.pullback (IsImmersion.liftCoborder i)).obj
    (Modules.quotientByIdeal
      (idealSheafSubobject (IsImmersion.liftCoborder i))
      (idealSheaf (IsImmersion.liftCoborder i)))

/-- The conormal sheaf is the coborder ideal quotient `I / I²`, pulled back along the
coborder closed immersion. -/
theorem conormalSheaf_eq {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] :
    conormalSheaf i =
      (Modules.pullback (IsImmersion.liftCoborder i)).obj
        (Modules.quotientByIdeal
          (idealSheafSubobject (IsImmersion.liftCoborder i))
          (idealSheaf (IsImmersion.liftCoborder i))) :=
  rfl

/-- The conormal sheaf of an immersion is the quasi-coherent `𝒪_Z`-module obtained from
the coborder closed immersion, its kernel ideal sheaf, and the successive quotient
`I / I²`. -/
theorem conormalSheaf_spec {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] :
    conormalSheaf i =
        (Modules.pullback (IsImmersion.liftCoborder i)).obj
          (Modules.quotientByIdeal
            (idealSheafSubobject (IsImmersion.liftCoborder i))
            (idealSheaf (IsImmersion.liftCoborder i))) ∧
      IsClosedImmersion (IsImmersion.liftCoborder i) ∧
      IsQuasiCoherent (idealSheafSubobject (IsImmersion.liftCoborder i)) :=
  sorry

/-- The conormal sheaf of an immersion of algebraic spaces is quasi-coherent. -/
instance instIsQuasicoherent_conormalSheaf {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsImmersion i] :
    (conormalSheaf i).IsQuasicoherent :=
  sorry

end Hom


end AlgebraicGeometry.AlgebraicSpace
