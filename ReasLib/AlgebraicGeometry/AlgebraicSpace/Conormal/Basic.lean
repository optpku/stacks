module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.CommRingSheafification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealQuotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.Coborder

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

/-- The quasi-coherent conormal module of an immersion, obtained by pulling back
the coborder ideal quotient `I / I²` to its source. -/
def Hom.conormalSheafQCoh {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsImmersion i] : QCoh Z :=
  { obj :=
    (Modules.pullback (IsImmersion.liftCoborder i)).obj
      (Modules.quotientByIdeal
        (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
        (Hom.idealSheaf (IsImmersion.liftCoborder i)))
    property := sorry }

/-- Commutative-ring-valued sheafification exists on the small étale site of an algebraic
space. -/
instance smallEtaleTopology_hasSheafify_commRingCat (X : AlgebraicSpace S) :
    HasSheafify (smallEtaleTopology X) CommRingCat.{u} :=
  CommRingSheafification.ofSpace X

/-- The coborder open `X \ ∂Z` supporting the closed-immersion factorization of an
immersion of algebraic spaces. -/
abbrev Hom.coborder {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] :
    AlgebraicSpace S :=
  (IsImmersion.coborderRange i).X

/-- `Hom.coborder i` is the underlying space of the coborder range of `i`. -/
theorem Hom.coborder_eq {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] :
    Hom.coborder i = (IsImmersion.coborderRange i).X :=
  rfl

/-- The conormal sheaf `C_{Z/X}` of an immersion of algebraic spaces, as the pullback
to `Z` of `I / I²` for the coborder closed immersion `Z ⟶ X \ ∂Z`. -/
abbrev Hom.conormalSheaf {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] :
    Z.Modules :=
  (Hom.conormalSheafQCoh i).obj

/-- The conormal sheaf is the coborder ideal quotient `I / I²`, pulled back along the
coborder closed immersion. -/
theorem Hom.conormalSheaf_eq {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] :
    Hom.conormalSheaf i =
      (Modules.pullback (IsImmersion.liftCoborder i)).obj
        (Modules.quotientByIdeal
          (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
          (Hom.idealSheaf (IsImmersion.liftCoborder i))) :=
  rfl

/-- The conormal sheaf of an immersion is the quasi-coherent `𝒪_Z`-module obtained from
the coborder closed immersion, its kernel ideal sheaf, and the successive quotient
`I / I²`. -/
theorem Hom.conormalSheaf_spec {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] :
    Hom.conormalSheaf i =
        (Modules.pullback (IsImmersion.liftCoborder i)).obj
          (Modules.quotientByIdeal
            (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
            (Hom.idealSheaf (IsImmersion.liftCoborder i))) ∧
      IsClosedImmersion (IsImmersion.liftCoborder i) ∧
      IsQuasiCoherent (Hom.idealSheafSubobject (IsImmersion.liftCoborder i)) :=
  sorry

/-- The conormal sheaf of an immersion of algebraic spaces is quasi-coherent. -/
theorem Hom.conormalSheaf_isQuasicoherent {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsImmersion i] :
    (Hom.conormalSheaf i).IsQuasicoherent :=
  (Hom.conormalSheafQCoh i).property

end AlgebraicGeometry.AlgebraicSpace
