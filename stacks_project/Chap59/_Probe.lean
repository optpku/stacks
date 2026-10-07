module
import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf
open CategoryTheory AlgebraicGeometry Opposite
universe u
#check Scheme.AffineOver.mk
#check Scheme.AffineOver.obj
#check Scheme.AffineOver.hom
#check AlgebraicGeometry.Spec.map
#check Scheme.Spec.map
#check Scheme.Spec.obj
#check CategoryTheory.evaluation
#check CategoryTheory.Functor.Elements.isInitialElementsMkShrinkYonedaObjObjEquivId
noncomputable def test {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    (Scheme.Spec.obj (op (CommRingCat.of A))).AffineOver :=
  Scheme.AffineOver.mk (Scheme.Spec.obj (op (CommRingCat.of B))) inferInstance
    (Spec.map (CommRingCat.ofHom f))
noncomputable def testhom {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    (test f).hom = Spec.map (CommRingCat.ofHom f) := by sorry
#check testhom
