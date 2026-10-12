/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.Scheme.DescentData

/-!
# Étale scheme descent data

The canonical descent datum obtained by pulling back a scheme étale over the base has an
étale component, so the canonical descent functor restricts to the corresponding full
subcategory.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DescentData

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The property that the unique component of singleton scheme descent data is étale over
`X`. -/
abbrev etaleProperty :
    ObjectProperty (DescentData (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f)) :=
  fun D ↦ AlgebraicGeometry.Etale (D.obj PUnit.unit).hom

/-- Singleton scheme descent data satisfy `etaleProperty f` exactly when their component is
étale over `X`. -/
theorem etaleProperty_iff
    (D : DescentData (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f)) :
    etaleProperty f D ↔ AlgebraicGeometry.Etale (D.obj PUnit.unit).hom := sorry

/-- Having an étale component is preserved by isomorphisms of singleton scheme descent data. -/
instance etalePropertyIsClosedUnderIsomorphisms :
    (etaleProperty f).IsClosedUnderIsomorphisms := sorry

/-- The category of singleton scheme descent data relative to `f` whose component is étale
over `X`. -/
abbrev Etale := (etaleProperty f).FullSubcategory

namespace Etale

/-- Bundle singleton scheme descent data whose component is étale. -/
def of (D : DescentData (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f))
    (hD : AlgebraicGeometry.Etale (D.obj PUnit.unit).hom) : Etale f :=
  ⟨D, hD⟩

/-- The underlying descent datum of `of D hD` is `D`. -/
theorem of_obj (D : DescentData (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f))
    (hD : AlgebraicGeometry.Etale (D.obj PUnit.unit).hom) :
    (of f D hD).obj = D := sorry

/-- The component of bundled étale descent data is canonically étale over `X`. -/
instance componentEtale (D : Etale f) :
    AlgebraicGeometry.Etale (D.obj.obj PUnit.unit).hom := sorry

/-- Forget that the component of singleton scheme descent data is étale. -/
def forget : Etale f ⥤ DescentData (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f) :=
  (etaleProperty f).ι

/-- The forgetful functor retains the underlying singleton scheme descent datum. -/
theorem forget_obj (D : Etale f) : (forget f).obj D = D.obj := sorry

/-- The canonical descent datum of a scheme étale over `S` has an étale component after
base change to `X`. -/
theorem canonicalFunctor_mapsTo (U : S.Etale) :
    etaleProperty f
      ((Scheme.Etale.forget S ⋙
        Scheme.overPseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ f)).obj U) := sorry

/-- Pullback along `f` sends schemes étale over `S` to singleton descent data with an étale
component over `X`. -/
noncomputable def canonicalFunctor : S.Etale ⥤ Etale f :=
  (etaleProperty f).lift
    (Scheme.Etale.forget S ⋙
      Scheme.overPseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ f))
    (canonicalFunctor_mapsTo f)

/-- Forgetting the étale-component condition identifies `canonicalFunctor f` with the
ambient canonical descent functor. -/
noncomputable def canonicalFunctorCompForgetIso :
    canonicalFunctor f ⋙ forget f ≅
      Scheme.Etale.forget S ⋙
        Scheme.overPseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ f) :=
  (etaleProperty f).liftCompιIso
    (Scheme.Etale.forget S ⋙
      Scheme.overPseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ f))
    (canonicalFunctor_mapsTo f)

/-- The component of the canonical étale descent datum is the pullback of the original scheme
along `f`. -/
theorem canonicalFunctor_obj_obj (U : S.Etale) :
    ((canonicalFunctor f).obj U).obj.obj PUnit.unit =
      (Over.pullback f).obj ((Scheme.Etale.forget S).obj U) := sorry

/-- On its unique component, the canonical étale descent functor maps a morphism by pullback
along `f`. -/
theorem canonicalFunctor_map_hom {U V : S.Etale} (g : U ⟶ V) :
    ((canonicalFunctor f).map g).hom.hom PUnit.unit =
      (Over.pullback f).map ((Scheme.Etale.forget S).map g) := sorry

end Etale

end AlgebraicGeometry.Scheme.DescentData
