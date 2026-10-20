module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverOpen

/-! # Base change of morphisms that are isomorphisms over an open -/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsoOverOpen

/-- Being an isomorphism over an open is stable under base change along any
morphism of algebraic spaces. -/
theorem baseChange_mem {S : Scheme.{u}} {V W U : AlgebraicSpace S}
    (f : V ⟶ W) (ι : U ⟶ W) [IsOpenImmersion ι] (X : IsoOverOpen ι) :
    isoOverOpenProperty (openInverseImageι f ι) ((overPullback f).obj X.obj) :=
  sorry

/-- Base change along `f : V ⟶ W` as a functor on iso-over-open slice
categories. The target open is the inverse image `f⁻¹U`. -/
def baseChange {S : Scheme.{u}} {V W U : AlgebraicSpace S}
    (f : V ⟶ W) (ι : U ⟶ W) [IsOpenImmersion ι] :
    IsoOverOpen ι ⥤ IsoOverOpen (openInverseImageι f ι) :=
  ObjectProperty.lift
    (isoOverOpenProperty (openInverseImageι f ι))
    (inclusion ι ⋙ overPullback f)
    (fun X ↦ baseChange_mem f ι X)

/-- After inclusion into the slice, `baseChange` is ordinary slice base change. -/
def baseChangeInclusionIso {S : Scheme.{u}} {V W U : AlgebraicSpace S}
    (f : V ⟶ W) (ι : U ⟶ W) [IsOpenImmersion ι] :
    baseChange f ι ⋙ inclusion (openInverseImageι f ι) ≅
      inclusion ι ⋙ overPullback f :=
  (isoOverOpenProperty (openInverseImageι f ι)).liftCompιIso
    (inclusion ι ⋙ overPullback f)
    (fun X ↦ baseChange_mem f ι X)

/-- The structure morphism of a `baseChange` object is the second projection
of the fibre product. -/
theorem baseChange_obj_hom {S : Scheme.{u}} {V W U : AlgebraicSpace S}
    (f : V ⟶ W) (ι : U ⟶ W) [IsOpenImmersion ι] (X : IsoOverOpen ι) :
    ((baseChange f ι).obj X).obj.hom = overPullbackSnd f X.obj :=
  sorry

end IsoOverOpen

end AlgebraicGeometry.AlgebraicSpace
