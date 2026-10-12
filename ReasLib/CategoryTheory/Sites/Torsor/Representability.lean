/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Presheaf.Representability
public import ReasLib.CategoryTheory.Sites.Torsor.GlobalSections

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace CategoryTheory.Sheaf.Torsor

/-- The functor sending a torsor to its underlying sheaf of sets. -/
def carrierFunctor
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {H : Sheaf J GrpCat.{max u v}} :
    Torsor.cat H ⥤ Sheaf J (Type (max u v)) where
  obj P := P.carrier
  map f := f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A trivial torsor under a group sheaf with representable carrier has representable carrier. -/
theorem carrier_isRepresentable_of_isTrivial
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {H : Sheaf J GrpCat.{max u v}}
    (hH : ((sheafForget J).obj H).1.IsRepresentable)
    (P : Torsor H) (hP : P.IsTrivial) :
    P.carrier.1.IsRepresentable := by
  rcases hP with ⟨eP⟩
  rcases hH.has_representation with ⟨X, ⟨R⟩⟩
  let eCarrier : ((sheafForget J).obj H) ≅ P.carrier := by
    simpa [carrierFunctor, Torsor.trivial] using
      ((carrierFunctor (H := H)).mapIso eP).symm
  let eCarrierVal :
      ((sheafForget J).obj H).1 ≅ P.carrier.1 :=
    (sheafToPresheaf J (Type (max u v))).mapIso eCarrier
  let eX :
      uliftYoneda.obj X ≅ ((sheafForget J).obj H).1 :=
    (Functor.RepresentableBy.equivUliftYonedaIso
      (((sheafForget J).obj H).1) X).toFun R
  exact
    ((Functor.RepresentableBy.equivUliftYonedaIso P.carrier.1 X).symm
      (eX ≪≫ eCarrierVal)).isRepresentable

/-- A torsor with a global section under a group sheaf with representable carrier has
representable carrier. -/
theorem carrier_isRepresentable_of_nonemptyGlobalSections
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type (max u v))]
    [HasGlobalSectionsFunctor J (Type (max u v))]
    {H : Sheaf J GrpCat.{max u v}}
    (hH : ((sheafForget J).obj H).1.IsRepresentable)
    (P : Torsor H) (hP : Nonempty ((Sheaf.Γ J (Type (max u v))).obj P.carrier)) :
    P.carrier.1.IsRepresentable := by
  exact carrier_isRepresentable_of_isTrivial hH P
    (isTrivial_of_nonempty_globalSections P hP)

end CategoryTheory.Sheaf.Torsor
