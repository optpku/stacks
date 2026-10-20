module

public import ReasLib.CategoryTheory.NatTrans.Arrow
public import Mathlib.AlgebraicTopology.DoldKan.PInfty
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The image of the complementary Dold--Kan projector

This file owns the canonical chain-level and degreewise images of `QInfty`. It does not depend on
the degreewise span presentation of degenerate simplices, so downstream developments can use the
projector image without importing that source-facing model.

@stack 019A
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Subobject
open AlgebraicTopology
open scoped Simplicial DoldKan

noncomputable section

universe v u

namespace AlgebraicTopology.DoldKan.QInfty

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The complementary Dold--Kan projector as a natural endomorphism of the alternating-face
complex functor. -/
@[stacks 019A "degenerate projector natural transformation"]
noncomputable def natTrans (C : Type u) [Category.{v} C] [Preadditive C] :
    alternatingFaceMapComplex C ⟶ alternatingFaceMapComplex C :=
  𝟙 _ - natTransPInfty C

/-- The component of the complementary-projector natural transformation is `QInfty`. -/
@[simp, stacks 019A "degenerate projector natural transformation component"]
theorem natTrans.app (U : SimplicialObject C) :
    (QInfty.natTrans C).app U = (QInfty : K[U] ⟶ K[U]) := sorry

/-- The complementary-projector natural transformation is idempotent. -/
@[reassoc, stacks 019A "degenerate projector idempotence"]
theorem natTrans_idem (C : Type u) [Category.{v} C] [Preadditive C] :
    QInfty.natTrans C ≫ QInfty.natTrans C = QInfty.natTrans C := sorry

section Image

variable [HasImages (ChainComplex C ℕ)]

/-- The image complex of `QInfty` at a simplicial object. -/
@[stacks 019A "canonical degenerate projector image complex"]
noncomputable def image (U : SimplicialObject C) : ChainComplex C ℕ :=
  Limits.image (QInfty : K[U] ⟶ K[U])

/-- The canonical projection from an alternating-face complex to the image of `QInfty`. -/
@[stacks 019A "canonical degenerate projector image projection"]
noncomputable def toImage (U : SimplicialObject C) : K[U] ⟶ QInfty.image U :=
  Limits.factorThruImage (QInfty : K[U] ⟶ K[U])

/-- The canonical inclusion of the image of `QInfty` into an alternating-face complex. -/
@[stacks 019A "canonical degenerate projector image inclusion"]
noncomputable def fromImage (U : SimplicialObject C) : QInfty.image U ⟶ K[U] :=
  Limits.image.ι (QInfty : K[U] ⟶ K[U])

/-- Projection to the image of `QInfty` followed by inclusion recovers the projector. -/
@[reassoc, stacks 019A "canonical degenerate projector image factorization"]
theorem toImage_comp_fromImage (U : SimplicialObject C) :
    QInfty.toImage U ≫ QInfty.fromImage U = (QInfty : K[U] ⟶ K[U]) := sorry

end Image

section ImageFunctor

variable [HasImages (ChainComplex C ℕ)] [HasImageMaps (ChainComplex C ℕ)]

/-- The canonical functorial image of the complementary Dold--Kan projector. -/
@[stacks 019A "canonical degenerate projector image functor"]
noncomputable def imageFunctor : SimplicialObject C ⥤ ChainComplex C ℕ :=
  (QInfty.natTrans C).imageFunctor

/-- The canonical projector-image functor takes `U` to `QInfty.image U`. -/
@[simp, stacks 019A "canonical degenerate projector image object formula"]
theorem imageFunctor.obj (U : SimplicialObject C) :
    (QInfty.imageFunctor (C := C)).obj U = QInfty.image U := sorry

namespace toImage

/-- The canonical projections to the images of `QInfty` form a natural transformation. -/
@[stacks 019A "canonical degenerate projector image projection natural transformation"]
noncomputable def natTrans :
    alternatingFaceMapComplex C ⟶ QInfty.imageFunctor (C := C) :=
  NatTrans.factorThruImage (QInfty.natTrans C)

/-- The component of the natural projection to the image of `QInfty` is `QInfty.toImage U`. -/
@[simp, stacks 019A "canonical degenerate projector image projection component"]
theorem natTrans.app (U : SimplicialObject C) :
    (QInfty.toImage.natTrans (C := C)).app U = QInfty.toImage U := sorry

end toImage

namespace fromImage

/-- The canonical inclusions from the images of `QInfty` form a natural transformation. -/
@[stacks 019A "canonical degenerate projector image inclusion natural transformation"]
noncomputable def natTrans :
    QInfty.imageFunctor (C := C) ⟶ alternatingFaceMapComplex C :=
  NatTrans.image.ι (QInfty.natTrans C)

/-- The component of the natural inclusion from the image of `QInfty` is
`QInfty.fromImage U`. -/
@[simp, stacks 019A "canonical degenerate projector image inclusion component"]
theorem natTrans.app (U : SimplicialObject C) :
    (QInfty.fromImage.natTrans (C := C)).app U = QInfty.fromImage U := sorry

end fromImage

/-- The natural projection to the images of `QInfty` followed by the natural inclusion recovers
the complementary projector. -/
@[reassoc, stacks 019A "canonical degenerate projector image natural factorization"]
theorem toImage.natTrans_comp_fromImage :
    QInfty.toImage.natTrans (C := C) ≫ QInfty.fromImage.natTrans (C := C) =
      QInfty.natTrans C := sorry

end ImageFunctor

section Split

variable [hI : HasImages (ChainComplex C ℕ)] [hE : HasStrongEpiImages (ChainComplex C ℕ)]

include hE

/-- The image inclusion followed by the image projection is the identity for the idempotent
`QInfty`. -/
@[reassoc, stacks 019A "canonical degenerate projector image retract law"]
theorem fromImage_comp_toImage (U : SimplicialObject C) :
    QInfty.fromImage U ≫ QInfty.toImage U = 𝟙 (QInfty.image U) := sorry

/-- The natural image inclusion followed by the natural image projection is the identity. -/
@[reassoc, stacks 019A "canonical degenerate projector image natural retract law"]
theorem fromImage.natTrans_comp_toImage :
    QInfty.fromImage.natTrans (C := C) ≫ QInfty.toImage.natTrans (C := C) =
      𝟙 (QInfty.imageFunctor (C := C)) := sorry

namespace fromImage

/-- The natural image inclusion of `QInfty`, equipped with its natural retraction. -/
@[stacks 019A "canonical degenerate projector image split monomorphism"]
noncomputable def splitMono :
    SplitMono (QInfty.fromImage.natTrans (C := C)) where
  retraction := QInfty.toImage.natTrans (C := C)
  id := QInfty.fromImage.natTrans_comp_toImage (C := C)

/-- The image inclusion of `QInfty` at `U`, equipped with its canonical retraction. -/
@[stacks 019A "canonical degenerate projector image component split monomorphism"]
noncomputable def appSplitMono (U : SimplicialObject C) :
    SplitMono (QInfty.fromImage U) where
  retraction := QInfty.toImage U
  id := QInfty.fromImage_comp_toImage U

/-- The natural image inclusion of `QInfty` is canonically split. -/
@[instance, stacks 019A "canonical degenerate projector image split monomorphism instance"]
theorem isSplitMono : IsSplitMono (QInfty.fromImage.natTrans (C := C)) := sorry

/-- Every component of the image inclusion of `QInfty` is canonically split. -/
@[instance, stacks 019A "canonical degenerate projector image component split monomorphism instance"]
theorem appIsSplitMono (U : SimplicialObject C) :
    IsSplitMono (QInfty.fromImage U) := sorry

end fromImage

namespace toImage

/-- The natural projection to the image of `QInfty`, equipped with its natural section. -/
@[stacks 019A "canonical degenerate projector image split epimorphism"]
noncomputable def splitEpi :
    SplitEpi (QInfty.toImage.natTrans (C := C)) where
  section_ := QInfty.fromImage.natTrans (C := C)
  id := QInfty.fromImage.natTrans_comp_toImage (C := C)

/-- The projection to the image of `QInfty` at `U`, equipped with its canonical section. -/
@[stacks 019A "canonical degenerate projector image component split epimorphism"]
noncomputable def appSplitEpi (U : SimplicialObject C) :
    SplitEpi (QInfty.toImage U) where
  section_ := QInfty.fromImage U
  id := QInfty.fromImage_comp_toImage U

/-- The natural projection to the image of `QInfty` is canonically split. -/
@[instance, stacks 019A "canonical degenerate projector image split epimorphism instance"]
theorem isSplitEpi : IsSplitEpi (QInfty.toImage.natTrans (C := C)) := sorry

/-- Every component of the projection to the image of `QInfty` is canonically split. -/
@[instance, stacks 019A "canonical degenerate projector image component split epimorphism instance"]
theorem appIsSplitEpi (U : SimplicialObject C) :
    IsSplitEpi (QInfty.toImage U) := sorry

end toImage

end Split

section DegreeImage

variable [HasImages C]

/-- The degree-`n` image subobject of the complementary Dold--Kan projector. -/
@[stacks 019A "degenerate projector degree image subobject"]
noncomputable def degreeSubobject (U : SimplicialObject C) (n : ℕ) :
    Subobject (U _⦋n⦌) :=
  Limits.imageSubobject ((QInfty : K[U] ⟶ K[U]).f n)

/-- The canonical projection to the degree-`n` image subobject of `QInfty`. -/
@[stacks 019A "degenerate projector degree image projection"]
noncomputable def degreeProjection (U : SimplicialObject C) (n : ℕ) :
    U _⦋n⦌ ⟶ (QInfty.degreeSubobject U n : C) :=
  Limits.factorThruImageSubobject ((QInfty : K[U] ⟶ K[U]).f n)

/-- The degreewise projection followed by the image-subobject inclusion is the component of
`QInfty`. -/
@[reassoc, stacks 019A "degenerate projector degree image factorization"]
theorem degreeProjection_comp_arrow (U : SimplicialObject C) (n : ℕ) :
    QInfty.degreeProjection U n ≫ (QInfty.degreeSubobject U n).arrow =
      (QInfty : K[U] ⟶ K[U]).f n := sorry

end DegreeImage

end AlgebraicTopology.DoldKan.QInfty
